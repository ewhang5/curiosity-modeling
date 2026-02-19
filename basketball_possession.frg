#lang forge/froglet

-- Load the visualization script
option run_sterling "layout.cnd"

// NBA Possession & Scoring Consistency Model

// Basic game structure
abstract sig Team {}
one sig TeamA, TeamB extends Team {}

abstract sig EventType {}
one sig ShotMade2, ShotMade3, ShotMissed, Turnover, Foul, OffensiveRebound, DefensiveRebound, ShotClockViolation, GameEnd extends EventType {}

sig State {
    scoreA: one Int,
    scoreB: one Int,
    possession: one Team,
    shotClock: one Int,
    event: lone EventType
}

one sig Game {
    firstState: one State,
    next: pfunc State -> State
}

// Structural constraints
pred wellformed {
    // Scores can never be negative, and NBA shot clocks are always between 0 and 24 seconds
    all s: State | {
        s.scoreA >= 0
        s.scoreB >= 0
        s.shotClock >= 0
        s.shotClock <= 24
    }
    
    // First state has no predecessor
    no prev: State | Game.next[prev] = Game.firstState
}

// Initialize the state
pred init[s: State] {
    s.scoreA = 0
    s.scoreB = 0
    s.shotClock = 24

    // The game cannot start in one of the following states
    s.event != OffensiveRebound
    s.event != DefensiveRebound
    s.event != ShotClockViolation
}

// State transition rules
pred validTransition[s1, s2: State] {
    one s1.event

    // Score a 2 pointer
    (s1.event = ShotMade2) => {
        // If TeamA, add 2 to scoreA
        (s1.possession = TeamA => {
            s2.scoreA = add[s1.scoreA, 2]
            s2.scoreB = s1.scoreB
        })
        
        // If TeamB, add 2 to scoreB
        (s1.possession = TeamB => {
            s2.scoreB = add[s1.scoreB, 2]
            s2.scoreA = s1.scoreA
        })

        // Possession changes and shot clock resets
        s2.possession != s1.possession
        s2.shotClock = 24
    }

    // Score a 3 pointer
    (s1.event = ShotMade3) => {
        // If TeamA, add 3 to scoreA
        (s1.possession = TeamA => {
            s2.scoreA = add[s1.scoreA, 3]
            s2.scoreB = s1.scoreB
        })

        // If TeamB, add 3 to scoreB
        (s1.possession = TeamB => {
            s2.scoreB = add[s1.scoreB, 3]
            s2.scoreA = s1.scoreA
        })

        // Possession changes and shot clock resets
        s2.possession != s1.possession
        s2.shotClock = 24
    }

    // If a shot is missed, scores don't change, no possession change in case of offensive rebound
    (s1.event = ShotMissed) => {
        s2.scoreA = s1.scoreA
        s2.scoreB = s1.scoreB
        s2.possession = s1.possession
        s2.shotClock = subtract[s1.shotClock, 1]
    }

    // If turnover, scores don't change, but possession changes and shot clock resets
    (s1.event = Turnover) => {
        s2.scoreA = s1.scoreA
        s2.scoreB = s1.scoreB
        s2.possession != s1.possession
        s2.shotClock = 24
    }

    // To simplify the model, only "on the floor" fouls will happen. These are fouls that do not award free throws.
    (s1.event = Foul) => {
        s2.scoreA = s1.scoreA
        s2.scoreB = s1.scoreB
        s2.possession = s1.possession

        // In the case that the shot clock is under 14 seconds, in the NBA, a foul causes it to reset back to 14 seconds
        (s1.shotClock < 14 => s2.shotClock = 14)
        (s1.shotClock >= 14 => s2.shotClock = s1.shotClock)
    }

    // Offensive rebounds do not change score or possession
    (s1.event = OffensiveRebound) => {
        s2.scoreA = s1.scoreA
        s2.scoreB = s1.scoreB
        s2.possession = s1.possession

        // In the case that the shot clock is under 14 seconds, in the NBA, an offensive rebound causes it to reset back to 14 seconds
        (s1.shotClock < 14 => s2.shotClock = 14)
        (s1.shotClock >= 14 => s2.shotClock = s1.shotClock)
    }

    // Defensive rebounds do not change score but change possession and reset shot clock
    (s1.event = DefensiveRebound) => {
        s2.scoreA = s1.scoreA
        s2.scoreB = s1.scoreB
        s2.possession != s1.possession
        s2.shotClock = 24
    }

    // Shot clock violation (clock reaches 0) flips the possession
    (s1.event = ShotClockViolation) => {
        s1.shotClock = 0
        s2.scoreA = s1.scoreA
        s2.scoreB = s1.scoreB
        s2.possession != s1.possession
        s2.shotClock = 24
    }
}

// Ensure game flows smoothly and realistically
pred gameFlow {
    all s: State | {
        // A Violation can ONLY exist if the clock is 0
        (s.event = ShotClockViolation) <=> (s.shotClock = 0)
        
        // Rebounds MUST be preceded by a missed shot
        (s.event = OffensiveRebound or s.event = DefensiveRebound) implies {
            some prev: State | Game.next[prev] = s and prev.event = ShotMissed
        }
        
        // Missed shots MUST be followed by a rebound
        (s.event = ShotMissed) implies {
            some nxt: State | Game.next[s] = nxt and (nxt.event = OffensiveRebound or nxt.event = DefensiveRebound)
        }

        // If the score changes, there needs to be a ShotMade event
        (some prev: State | Game.next[prev] = s and (s.scoreA != prev.scoreA or s.scoreB != prev.scoreB)) implies {
            all prev: State | Game.next[prev] = s implies (prev.event = ShotMade2 or prev.event = ShotMade3)
        }

        // If there is no next state, the game ends
        (no Game.next[s]) <=> s.event = GameEnd
    }
}

// Trace constraints
pred traces {
    wellformed
    init[Game.firstState]
    all s: State | some Game.next[s] implies validTransition[s, Game.next[s]]
    gameFlow
}


// Run command
run {
    traces
} for 5 State, 6 Int for { next is linear }