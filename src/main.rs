// Our goal is to prove that a particular machine loops forever.
// In order to do this, we need to demonstrate that every state has a successor state.

// A state is tuple:
// - current state
// - current bit
// - left string
// - right string

// For example, 101 0C 111

// Note that if there are initial 0s in the left string, or trailing 0s in the right
// string, they can be removed without changing the identity of the state.

// However, there's no obvious way to produce a proof for _all_ states unless the exact
// same state is revisted multiple times (i.e. "looping").

// Instead, we produce an _approximation_ of states. Specifically, an _abstraction_ is
// a representation for some (possibly infinite) set of states. For example,
// 101 0C 1^n is an abstraction that includes 101 0C 1, 101 0C 11, 101 0C 111, etc.

// We must prove that if s is _any_ state in abstraction A, that its successor will belong
// to one of a finite set of abstractions B_1, ..., B_k. If we can do the same for each of
// these abstractions, then we are done.

// At all times, we have a set of "targets" which must be processed. Each target can be
// processed in one of several ways:
// - evaluation: if possible, directly execute one step of the program
// - abstraction: replace the current concrete state with an abstract set that includes it
// - widening: replace the current abstract set with a larger abstract set that includes all of it

// All targets are compared for exact equality. If we've already processed a target, then we
// know it has a successor, so there's no need to continue.

// If the number of targets grows too large, we fail.

use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
enum Color {
    A,
    B,
    C,
    D,
    E,
}

impl Display for Color {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Color::A => "A",
            Color::B => "B",
            Color::C => "C",
            Color::D => "D",
            Color::E => "E",
        })
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
enum Bit {
    B0,
    B1,
}

impl Display for Bit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Bit::B0 => "0",
            Bit::B1 => "1",
        })
    }
}

// This tape must be finite.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Tape {
    words: Vec<Word>,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
enum Word {
    Bit(Bit),
    Repeat(Tape), // MIN_REPEAT_COUNT or more of the element tape.
    Any,          // Any string of bits, even an empty one.
}

impl Display for Word {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Word::Bit(b) => {
                f.write_fmt(format_args!("{b}"))?;
            }
            Word::Repeat(b) => {
                f.write_str("{")?;
                f.write_fmt(format_args!("{}", b))?;
                f.write_str("}")?;
            }
            Word::Any => {
                f.write_str("any")?;
            }
        }

        Ok(())
    }
}

// This tape is implicitly followed by infinitely many 0s.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct InfTape {
    start: Tape,
}

impl InfTape {
    // Trailing zeros should be removed.
    fn canonical(mut self, min_repeat_count: usize) -> Self {
        self.start = self.start.canonical(min_repeat_count);
        while self.start.words.last() == Some(&Word::Bit(Bit::B0)) {
            self.start.words.pop();
        }
        self
    }

    fn cons(&self, b: Bit, min_repeat_count: usize) -> InfTape {
        let mut res = self.clone();
        res.start = res.start.cons(b, min_repeat_count);
        res.canonical(min_repeat_count)
    }

    fn split(&self, min_repeat_count: usize) -> HashSet<(Bit, InfTape)> {
        let mut result = HashSet::new();
        for out in self.start.split(min_repeat_count) {
            match out {
                None => {
                    result.insert((
                        Bit::B0,
                        InfTape {
                            start: Tape { words: vec![] },
                        },
                    ));
                }
                Some((b, trail)) => {
                    result.insert((b, InfTape { start: trail }));
                }
            }
        }

        result
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Target {
    color: Color,
    head: Bit,
    right: InfTape,
    left: InfTape, // note: effectively backwards
}

impl Target {
    fn canonical(self, min_repeat_count: usize) -> Self {
        Target {
            left: self.left.canonical(min_repeat_count),
            right: self.right.canonical(min_repeat_count),
            ..self
        }
    }
}

impl Display for Target {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "{} {} // {} // {}",
            self.color, self.head, self.left.start, self.right.start
        ))?;

        Ok(())
    }
}

impl Display for Tape {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for x in self.words.iter() {
            f.write_fmt(format_args!("{x}"))?;
        }
        Ok(())
    }
}

impl Tape {
    fn cons(&self, b: Bit, min_repeat_count: usize) -> Tape {
        let mut words = vec![Word::Bit(b)];
        words.extend(self.words.iter().cloned());
        Tape { words }.canonical(min_repeat_count)
    }

    fn cat(&self, other: &Tape) -> Tape {
        let mut words = self.words.clone();
        words.extend(other.words.iter().cloned());
        Tape { words }
    }

    // If None, then this tape was empty.
    // Otherwise, the first bit, and the tape that followed.
    fn split(&self, min_repeat_count: usize) -> HashSet<Option<(Bit, Tape)>> {
        if self.words.is_empty() {
            // Must be empty.
            return vec![None].into_iter().collect();
        }

        match &self.words[0] {
            Word::Bit(b) => {
                // It must start with this bit, with the rest following.
                vec![Some((
                    *b,
                    Tape {
                        words: self.words[1..].to_vec(),
                    },
                ))]
                .into_iter()
                .collect()
            }
            Word::Repeat(rep) => {
                let remove_from_rep = rep.split(min_repeat_count);

                if remove_from_rep.contains(&None) {
                    // Each repeating unit might be empty.
                    // If this can happen, we have a bug.
                    panic!("this is not allowed: repeating strings must never be empty");
                } else {
                    // It cannot be empty. So the first bit definitely comes from the first
                    // occurrence.
                    // There are either MIN_REPEAT_COUNT-1 that follow it, or there is another that follows it.
                    // So, expand in both ways.

                    let mut combined_results = HashSet::new();

                    for pair in remove_from_rep.iter() {
                        let (bit, rest) = match pair {
                            Some(pair) => pair,
                            None => {
                                panic!("this case was ruled out above");
                            }
                        };

                        // Followed by MIN_REPEAT_COUNT-1 of the pattern.
                        let mut base_case_words = rest.words.clone();
                        for _ in 0..min_repeat_count - 1 {
                            base_case_words.extend(rep.words.iter().cloned());
                        }
                        base_case_words.extend(self.words[1..].iter().cloned());
                        combined_results.insert(Some((
                            *bit,
                            Tape {
                                words: base_case_words,
                            },
                        )));

                        // Followed by the rest, then by self, which is (rep)+N R
                        combined_results.insert(Some((*bit, rest.cat(self))));
                    }

                    combined_results
                }
            }
            Word::Any => {
                if self.words.len() != 1 {
                    panic!("any can occur at the last position");
                }
                vec![
                    None,
                    Some((Bit::B0, self.clone())),
                    Some((Bit::B1, self.clone())),
                ]
                .into_iter()
                .collect()
            }
        }
    }

    fn make_abstract(&self, min_repeat_count: usize) -> Option<Tape> {
        for i in 0..self.words.len() {
            if let Word::Repeat(rep) = &self.words[i] {
                if let Some(improved) = rep.make_abstract(min_repeat_count) {
                    let mut new_tape = self.clone();
                    new_tape.words[i] = Word::Repeat(improved);
                    return Some(new_tape);
                }
            }
        }
        // Start from the back.
        // If we find a repeat, preceded by its member, extend it.
        for i in (0..self.words.len()).rev() {
            if let Word::Repeat(rep) = &self.words[i] {
                // R {R}+  -->  {R}+
                if rep.words.len() <= i && self.words[i - rep.words.len()..i] == rep.words {
                    let mut excised_repeat = self.clone();
                    excised_repeat.words.drain(i - rep.words.len()..i);
                    return Some(excised_repeat);
                }

                // {R}+ R  -->  {R}+
                if i + 1 + rep.words.len() <= self.words.len()
                    && self.words[i + 1..i + 1 + rep.words.len()] == rep.words
                {
                    let mut excised_repeat = self.clone();
                    excised_repeat.words.drain(i + 1..i + 1 + rep.words.len());
                    return Some(excised_repeat);
                }

                if i >= 1 && self.words[i - 1] == self.words[i] {
                    // Two adjacent reps; merge them.
                    let mut excised_repeat = self.clone();
                    excised_repeat.words.remove(i - 1);
                    return Some(excised_repeat);
                }
            }
        }

        // If we find a contiguous group of the same value repeated MIN_REPEAT_COUNT times,
        // abstract it into a repeat.
        for i in (0..self.words.len()).rev() {
            for len in 1..i {
                if len * min_repeat_count <= i {
                    // For each repetition, check that it's equal.
                    let mut all_equal = true;
                    for j in 1..min_repeat_count {
                        if self.words[i - len + 1..=i]
                            != self.words[i - len + 1 - len * j..=i - len * j]
                        {
                            all_equal = false;
                        }
                    }
                    if all_equal {
                        let mut excised_repeat = self.clone();
                        let repeated = Word::Repeat(Tape {
                            words: self.words[i - len + 1..=i].to_vec(),
                        });
                        excised_repeat.words.insert(i + 1, repeated);
                        excised_repeat
                            .words
                            .drain(i - len * min_repeat_count + 1..=i);
                        return Some(excised_repeat);
                    }
                }
            }
        }

        if self.words.len() >= 10 {
            let mut res = self.clone();
            for _ in 0..5 {
                res.words.pop();
            }
            res.words.push(Word::Any);
            return Some(res);
        }

        None
    }

    fn canonical(mut self, min_repeat_count: usize) -> Tape {
        while let Some(next) = self.make_abstract(min_repeat_count) {
            self = next;
        }
        self
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
enum Dir {
    Left,
    Right,
}

#[derive(Debug, Copy, Clone)]
struct RuleThen {
    new_color: Color,
    dir: Dir,
    write: Bit,
}

#[derive(Clone, Debug)]
struct Rules {
    by_case: HashMap<(Bit, Color), RuleThen>,
}

impl Rules {
    fn from_string(s: &str) -> Rules {
        if s.len() == 34 || s.len() == 30 {
            let s = s.as_bytes();
            let mut rules = Rules {
                by_case: HashMap::new(),
            };

            fn color_from_char(c: u8) -> Color {
                if c == b'A' {
                    return Color::A;
                }
                if c == b'B' {
                    return Color::B;
                }
                if c == b'C' {
                    return Color::C;
                }
                if c == b'D' {
                    return Color::D;
                }
                if c == b'E' {
                    return Color::E;
                }
                panic!("unknown color {}", c);
            }
            fn bit_from_char(c: u8) -> Bit {
                if c == b'0' {
                    return Bit::B0;
                }
                if c == b'1' {
                    return Bit::B1;
                }
                panic!("unknown bit {}", c);
            }
            fn dir_from_char(c: u8) -> Dir {
                if c == b'R' {
                    return Dir::Right;
                }
                if c == b'L' {
                    return Dir::Left;
                }
                panic!("unknown dir {}", c);
            }

            for color in [
                (Color::A, 0),
                (Color::B, 1),
                (Color::C, 2),
                (Color::D, 3),
                (Color::E, 4),
            ] {
                for bit in [(Bit::B0, 0), (Bit::B1, 1)] {
                    let i = color.1 * (if s.len() == 34 { 7 } else { 6 }) + bit.1 * 3;

                    if s[i] == b'-' {
                        // Halting state.
                        continue;
                    }

                    let conc = RuleThen {
                        new_color: color_from_char(s[i + 2]),
                        dir: dir_from_char(s[i + 1]),
                        write: bit_from_char(s[i]),
                    };

                    rules.by_case.insert((bit.0, color.0), conc);
                }
            }

            return rules;
        }

        panic!("unknown format, expected a 34-character string like '1RB0LC_0LA1RD_1LA0RB_1LE---_0RA1RE' or a 30-character string like '1RB0LC0LA1RD1LA0RB1LE---0RA1RE'");
    }
}

use clap::Parser;
#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct Args {
    // The machine to handle, in 30-character or 34-character format.
    #[clap(
        short,
        long,
        value_parser,
        help = "A machine, as either a 34-character string '1RB0LC_0LA1RD_1LA0RB_1LE---_0RA1RE' or a 30-character string like '1RB0LC0LA1RD1LA0RB1LE---0RA1RE'."
    )]
    machine: String,

    #[clap(
        long,
        value_parser,
        default_value_t = 1_000_000,
        help = "The maximum number of iterations to run before giving up."
    )]
    max_iterations: u64,

    #[clap(
        long,
        value_parser,
        default_value_t = 4,
        help = "The number of times that a sequence must repeat before being abstracted. In some cases, larger values like 4 or 10 work better."
    )]
    min_repeat_count: usize,

    #[clap(short, long, value_parser)]
    verbose: bool,
}

fn main() -> Result<(), i32> {
    let args = Args::parse();

    let min_repeat_count = args.min_repeat_count;

    // Examples:

    // Success:
    // - 1RB0LC_0LA1RD_1LA0RB_1LE---_0RA1RE
    // - 1RB0LD_0LC0RD_1LA1LB_1LA1RE_0LA---
    // - 1RB1RD_1LC0RB_0LD1LA_0RA0LE_1LD---
    // - 1RB---_0LC1RA_1RB1LD_1RC0LE_0RA0RB
    // - 1RB0RC_0LC---_1RD1RC_0LE1RA_1RD1LE
    // - All 3 cyclers
    // - All 4 unilateral bouncers
    // - All 3 bilateral bouncers
    // - All 4 translated cyclers

    // Fails:
    // - 1RB0LD_1LC1RC_1LA0RC_---0LE_0RB1LD (crash)
    // - 1RB0RD_1LC1LB_1RA0LB_0RE1RD_---1RA (crash)
    // - 1RB0RB_1LC0RD_1LD1LB_0RA0RE_---1RD (translated unilateral bouncer, crash)
    // - All exponential counters
    // - 1RB1RC_1RC1RE_0RD0RC_1LD1LA_---1RB (bell, crash)
    // - 1RB0RA_1LB1RC_1RA1LD_1LE0LD_1LC--- (exponential counter, crash)

    let machine = Rules::from_string(&args.machine);

    let mut states = vec![Target {
        color: Color::A, // initial state,
        head: Bit::B0,   // tape is blank,
        left: InfTape {
            start: Tape { words: vec![] },
        },
        right: InfTape {
            start: Tape { words: vec![] },
        },
    }];
    let mut states_processed: HashSet<Target> = states.clone().into_iter().collect();

    let mut maximum_runtime = args.max_iterations;

    while let Some(state) = states.pop() {
        if maximum_runtime == 0 {
            eprintln!("took too long, stopping");
            return Err(1);
        }
        maximum_runtime -= 1;

        if args.verbose {
            eprintln!("{}", state);
        }

        // Try to step once forward, producing a new state.
        if let Some(rule_then) = machine.by_case.get(&(state.head, state.color)) {
            match rule_then.dir {
                Dir::Left => {
                    // Extract the new head from the left:
                    for (new_bit, rest) in state.left.split(min_repeat_count) {
                        // Create the new state.
                        let new_state = Target {
                            color: rule_then.new_color,
                            head: new_bit,
                            left: rest,
                            right: state.right.cons(rule_then.write, min_repeat_count),
                        }
                        .canonical(min_repeat_count);

                        if !states_processed.contains(&new_state) {
                            states_processed.insert(new_state.clone());
                            states.push(new_state);
                        }
                    }
                }
                Dir::Right => {
                    // Extract the new head from the right:
                    for (new_bit, rest) in state.right.split(min_repeat_count) {
                        // Create the new state.
                        let new_state = Target {
                            color: rule_then.new_color,
                            head: new_bit,
                            right: rest,
                            left: state.left.cons(rule_then.write, min_repeat_count),
                        }
                        .canonical(min_repeat_count);

                        if !states_processed.contains(&new_state) {
                            states_processed.insert(new_state.clone());
                            states.push(new_state);
                        }
                    }
                }
            }
        } else {
            eprintln!(
                "Analysis failed. This machine might halt at state {}",
                state
            );
            return Err(1);
        }
    }

    println!("Machine '{}' terminates", args.machine);
    Ok(())
}
