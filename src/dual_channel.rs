#![deny(missing_docs)]

//! This module implements `ChannelTerminal`, meant to be used in pairs of its
//! instances with crossed `Sender`s and `Receiver` from `mpsc::channel`. This
//! crossing is performed in `pair_terminals`. The idea is that one terminal can
//! send/receive messages to/from the other.

use anyhow::{anyhow, Result};
use std::sync::mpsc::{channel, Iter, Receiver, Sender};

/// Holds a `Sender` and a `Receiver` which are not expected to be paired with
/// each other
pub struct ChannelTerminal<T> {
    sender: Sender<T>,
    receiver: Receiver<T>,
}

impl<T> ChannelTerminal<T> {
    /// Sends a message through its inner `Sender`
    #[inline]
    pub fn send(&self, t: T) -> Result<()> {
        self.sender.send(t).map_err(|e| anyhow!(e.to_string()))
    }

    /// Receives a message through its inner `Receiver`, blocking the current thread
    #[inline]
    #[allow(dead_code)]
    pub fn recv(&self) -> Result<T> {
        self.receiver.recv().map_err(|e| anyhow!(e.to_string()))
    }

    /// Collects all the messages received so far and materializes them in a
    /// vector without blocking the current thread
    #[inline]
    pub fn collect(&self) -> Vec<T> {
        self.receiver.try_iter().collect()
    }

    #[inline]
    /// Returns a thread-blocking iterator for the received messages
    pub fn iter(&self) -> Iter<'_, T> {
        self.receiver.iter()
    }
}

/// Creates a pair of `ChannelTerminal` with crossed senders and receivers such
/// that one terminal can send/receive messages to/from the other
pub fn pair_terminals<T>() -> (ChannelTerminal<T>, ChannelTerminal<T>) {
    let (sender_terminal_1, receiver_terminal_2) = channel();
    let (sender_terminal_2, receiver_terminal_1) = channel();
    (
        ChannelTerminal {
            sender: sender_terminal_1,
            receiver: receiver_terminal_1,
        },
        ChannelTerminal {
            sender: sender_terminal_2,
            receiver: receiver_terminal_2,
        },
    )
}

/// Creates a dummy `ChannelTerminal` that just sends messages to itself
#[inline]
pub fn dummy_terminal<T>() -> ChannelTerminal<T> {
    let (sender, receiver) = channel();
    ChannelTerminal { sender, receiver }
}

#[cfg(test)]
pub mod tests {
    #[test]
    fn test_terminals() {
        let (t1, t2) = super::pair_terminals::<&str>();

        t1.send("hi from t1").unwrap();
        t2.send("hi from t2").unwrap();

        assert_eq!(t1.recv().unwrap(), "hi from t2");
        assert_eq!(t2.recv().unwrap(), "hi from t1");
    }
}
