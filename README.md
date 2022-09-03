# A toy decider for the [BBChallenge](https://bbchallenge.org/)

This decider works by abstract interpretation on Turing Machine states. Each state is represented as essentially a regex like `100{110}01{0} 1C {1}`.
A pattern like `{110}` represents `N` or more occurrences of the string `110`, with `N` configurable by the `--min-repeat-count` flag.

The provided machine is run, one step at a time, until:

- the current state could halt, in which case search has failed
- all reachable states have been explored, confirming that the machine does not halt
- time runs out (configurable by `--max-iterations`)

Whenever `--min-repeat-count` or more occurrences of the same string occur within a state, they're automatically abstracted to a repeated clause (for example, with `--min-repeat-count 4`, the string `0010110110100` becomes `00{101}00`).
Other automatic abstractions likewise reduce the number of possibilities considered:

- `X{X}` -> `{X}`
- `{X}{X}` -> `{X}`
- `{X}X` -> `{X}`

This approach works well on "bouncing" Turing Machines, though not very well on "translating" machines that drift over time.
