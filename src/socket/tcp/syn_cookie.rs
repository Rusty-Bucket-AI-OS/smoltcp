#![cfg_attr(not(test), allow(dead_code))]

//! Stateless SYN cookies for listening TCP sockets (see RFC 4987, section 3.6).
//!
//! A server under a SYN flood cannot afford a connection record for every SYN. With a cookie it
//! keeps none: the initial sequence number it sends in the SYN|ACK is a keyed hash of the
//! connection's endpoints, the client's own sequence number and a coarse clock, plus an index
//! into a small table of MSS values. The client's final ACK echoes that number plus one, so a
//! valid ACK proves the client received the SYN|ACK, and the number gives back everything the
//! server needs to create the connection.
//!
//! The cookie is `h1 + client_isn + (t << 24) + ((h2 + mss_index) & 0xFF_FFFF)` with wrapping
//! arithmetic, where `h1` and `h2` are different keyed hashes (SipHash-2-4) over the
//! endpoints, the client's sequence number and the period `t`. A forged ACK is accepted with a
//! chance of about 2^-22, and a cookie is good only for the sequence number it was made for.

use crate::wire::{IpAddress, IpEndpoint};

/// The secret that cookies are made with. It must come from a good random source.
pub(super) type Key = [u8; 16];

/// The MSS values a cookie can carry. The client's offer is rounded down to one of them.
pub(super) const MSS_TABLE: [u16; 4] = [536, 1220, 1440, 1460];

/// Seconds in one clock period of a cookie.
const PERIOD_SECS: u64 = 64;

/// A cookie is good for the period it was made in and this many periods after it.
const MAX_AGE: u32 = 1;

/// The two endpoints of a connection, from the server's side.
pub(super) struct Ends<'a> {
    pub(super) remote: &'a IpEndpoint,
    pub(super) local: &'a IpEndpoint,
}

fn put_addr(msg: &mut [u8; 48], at: usize, addr: IpAddress) -> usize {
    match addr {
        #[cfg(feature = "proto-ipv4")]
        IpAddress::Ipv4(a) => {
            msg[at..at + 4].copy_from_slice(&a.octets());
            at + 4
        }
        #[cfg(feature = "proto-ipv6")]
        IpAddress::Ipv6(a) => {
            msg[at..at + 16].copy_from_slice(&a.octets());
            at + 16
        }
    }
}

fn hash(key: &Key, ends: &Ends, client_isn: u32, period: u32, salt: u8) -> u32 {
    // salt, period, client_isn, ports, then both addresses (at most 4 + 4 + 1 + 4 + 32 = 45).
    let mut msg = [0u8; 48];
    msg[0] = salt;
    msg[1..5].copy_from_slice(&period.to_be_bytes());
    msg[5..9].copy_from_slice(&client_isn.to_be_bytes());
    msg[9..11].copy_from_slice(&ends.remote.port.to_be_bytes());
    msg[11..13].copy_from_slice(&ends.local.port.to_be_bytes());
    let end = put_addr(&mut msg, 13, ends.remote.addr);
    let end = put_addr(&mut msg, end, ends.local.addr);
    siphash24(key, &msg[..end]) as u32
}

/// The cookie to send as the initial sequence number in answer to a SYN with sequence number
/// `client_isn` and MSS option `mss`, at `now_secs` seconds.
pub(super) fn issue(key: &Key, ends: &Ends, client_isn: u32, mss: u16, now_secs: u64) -> u32 {
    let period = (now_secs / PERIOD_SECS) as u32;
    let index = MSS_TABLE.iter().rposition(|m| *m <= mss).unwrap_or(0) as u32;
    hash(key, ends, client_isn, period, 1)
        .wrapping_add(client_isn)
        .wrapping_add(period << 24)
        .wrapping_add(hash(key, ends, client_isn, period, 2).wrapping_add(index) & 0x00FF_FFFF)
}

/// Checks the ACK that ends a handshake. `cookie` is its acknowledgement number minus one,
/// `client_isn` its sequence number minus one. Returns the MSS the cookie carried.
pub(super) fn check(
    key: &Key,
    ends: &Ends,
    client_isn: u32,
    cookie: u32,
    now_secs: u64,
) -> Option<u16> {
    let now = (now_secs / PERIOD_SECS) as u32;
    for age in 0..=MAX_AGE {
        let period = now.wrapping_sub(age);
        let rest = cookie
            .wrapping_sub(hash(key, ends, client_isn, period, 1))
            .wrapping_sub(client_isn)
            .wrapping_sub(period << 24);
        let index = rest.wrapping_sub(hash(key, ends, client_isn, period, 2)) & 0x00FF_FFFF;
        if rest >> 24 == 0 && (index as usize) < MSS_TABLE.len() {
            return Some(MSS_TABLE[index as usize]);
        }
    }
    None
}

/// SipHash-2-4 (Aumasson and Bernstein): a keyed hash for short inputs.
fn siphash24(key: &Key, data: &[u8]) -> u64 {
    let k0 = u64::from_le_bytes([
        key[0], key[1], key[2], key[3], key[4], key[5], key[6], key[7],
    ]);
    let k1 = u64::from_le_bytes([
        key[8], key[9], key[10], key[11], key[12], key[13], key[14], key[15],
    ]);
    let mut v = [
        k0 ^ 0x736f_6d65_7073_6575,
        k1 ^ 0x646f_7261_6e64_6f6d,
        k0 ^ 0x6c79_6765_6e65_7261,
        k1 ^ 0x7465_6462_7974_6573,
    ];
    let round = |v: &mut [u64; 4]| {
        v[0] = v[0].wrapping_add(v[1]);
        v[1] = v[1].rotate_left(13) ^ v[0];
        v[0] = v[0].rotate_left(32);
        v[2] = v[2].wrapping_add(v[3]);
        v[3] = v[3].rotate_left(16) ^ v[2];
        v[0] = v[0].wrapping_add(v[3]);
        v[3] = v[3].rotate_left(21) ^ v[0];
        v[2] = v[2].wrapping_add(v[1]);
        v[1] = v[1].rotate_left(17) ^ v[2];
        v[2] = v[2].rotate_left(32);
    };
    let mut chunks = data.chunks_exact(8);
    for c in &mut chunks {
        let m = u64::from_le_bytes([c[0], c[1], c[2], c[3], c[4], c[5], c[6], c[7]]);
        v[3] ^= m;
        round(&mut v);
        round(&mut v);
        v[0] ^= m;
    }
    let rest = chunks.remainder();
    let mut last = [0u8; 8];
    last[..rest.len()].copy_from_slice(rest);
    last[7] = data.len() as u8;
    let m = u64::from_le_bytes(last);
    v[3] ^= m;
    round(&mut v);
    round(&mut v);
    v[0] ^= m;
    v[2] ^= 0xff;
    for _ in 0..4 {
        round(&mut v);
    }
    v[0] ^ v[1] ^ v[2] ^ v[3]
}

#[cfg(test)]
mod test {
    use super::*;

    cfg_if::cfg_if! {
        if #[cfg(feature = "proto-ipv4")] {
            fn addr(n: u8) -> IpAddress {
                IpAddress::v4(10, 0, 0, n)
            }
        } else {
            fn addr(n: u8) -> IpAddress {
                IpAddress::v6(0xfe80, 0, 0, 0, 0, 0, 0, n as u16)
            }
        }
    }

    const KEY: Key = [
        0x13, 0x37, 0xc0, 0xde, 0x01, 0x02, 0x03, 0x04, 0x99, 0x98, 0x97, 0x96, 0x55, 0x44, 0x33,
        0x22,
    ];

    fn ends<'a>(remote: &'a IpEndpoint, local: &'a IpEndpoint) -> Ends<'a> {
        Ends { remote, local }
    }

    #[test]
    fn siphash_matches_the_published_vectors() {
        // From the SipHash paper: key 00 01 .. 0f, message 00 01 .. 0e (15 bytes).
        let key: Key = core::array::from_fn(|i| i as u8);
        let msg: [u8; 15] = core::array::from_fn(|i| i as u8);
        assert_eq!(siphash24(&key, &msg), 0xa129_ca61_49be_45e5);
        // And the empty message (the reference implementation's first vector).
        assert_eq!(siphash24(&key, &[]), 0x726f_db47_dd0e_0e31);
    }

    #[test]
    fn a_cookie_round_trips_with_the_mss_rounded_down() {
        let (remote, local) = (
            IpEndpoint::new(addr(2), 40000),
            IpEndpoint::new(addr(1), 80),
        );
        let e = ends(&remote, &local);
        for (offered, carried) in [
            (0, 536),
            (100, 536),
            (536, 536),
            (1000, 536),
            (1220, 1220),
            (1439, 1220),
            (1440, 1440),
            (1460, 1460),
            (9000, 1460),
        ] {
            let c = issue(&KEY, &e, 0xdead_beef, offered, 1000);
            assert_eq!(
                check(&KEY, &e, 0xdead_beef, c, 1000),
                Some(carried),
                "{offered}"
            );
        }
    }

    #[test]
    fn a_cookie_lasts_two_periods_and_no_longer() {
        let (remote, local) = (
            IpEndpoint::new(addr(2), 40000),
            IpEndpoint::new(addr(1), 80),
        );
        let e = ends(&remote, &local);
        let c = issue(&KEY, &e, 7, 1460, 100); // period 1 (64..128)
        assert!(check(&KEY, &e, 7, c, 100).is_some());
        assert!(check(&KEY, &e, 7, c, 127).is_some());
        assert!(check(&KEY, &e, 7, c, 128).is_some(), "the next period");
        assert!(check(&KEY, &e, 7, c, 191).is_some());
        assert!(check(&KEY, &e, 7, c, 192).is_none(), "two periods on");
        assert!(check(&KEY, &e, 7, c, 100_000).is_none());
        // From the past is no good either (the clock never goes back for a cookie we made).
        assert!(check(&KEY, &e, 7, c, 10).is_none());
    }

    #[test]
    fn a_cookie_fits_only_its_connection_sequence_number_and_key() {
        let (remote, local) = (
            IpEndpoint::new(addr(2), 40000),
            IpEndpoint::new(addr(1), 80),
        );
        let e = ends(&remote, &local);
        let c = issue(&KEY, &e, 1000, 1460, 500);
        let other_port = IpEndpoint::new(addr(2), 40001);
        let other_addr = IpEndpoint::new(addr(3), 40000);
        let other_local = IpEndpoint::new(addr(1), 81);
        assert!(check(&KEY, &ends(&other_port, &local), 1000, c, 500).is_none());
        assert!(check(&KEY, &ends(&other_addr, &local), 1000, c, 500).is_none());
        assert!(check(&KEY, &ends(&remote, &other_local), 1000, c, 500).is_none());
        assert!(check(&KEY, &e, 1001, c, 500).is_none());
        assert!(check(&KEY, &e, 999, c, 500).is_none());
        let mut other_key = KEY;
        other_key[3] ^= 1;
        assert!(check(&other_key, &e, 1000, c, 500).is_none());
        assert!(check(&KEY, &e, 1000, c ^ 1, 500).is_none());
        assert!(check(&KEY, &e, 1000, c.wrapping_add(1), 500).is_none());
    }

    #[test]
    fn guessed_cookies_are_almost_never_accepted() {
        let (remote, local) = (
            IpEndpoint::new(addr(2), 40000),
            IpEndpoint::new(addr(1), 80),
        );
        let e = ends(&remote, &local);
        // A simple generator with a fixed seed (the test is the same every run).
        let mut x: u64 = 0x2545_f491_4f6c_dd1d;
        let mut accepted = 0;
        for _ in 0..20_000 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            if check(&KEY, &e, 5, x as u32, 500).is_some() {
                accepted += 1;
            }
        }
        // The chance is about 2 * 4 / 2^24 per guess: 20,000 guesses accept none.
        assert_eq!(accepted, 0);
    }
}
