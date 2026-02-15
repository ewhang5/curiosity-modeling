#lang forge/froglet

-- Load the visualization script
option run_sterling "layout.cnd"

// NBA Possession & Scoring Consistency Model

// Boolean encodings
abstract sig Boolean {}
one sig True, False extends Boolean {}

// Basic game structure
abstract sig Team {}
one sig TeamA, TeamB extends Team {}

abstract sig EventType {}
one sig ShotMade2, ShotMade3, ShotMissed, Turnover, Foul, OffensiveRebound, DefensiveRebound extends EventType {}

sig State {
    scoreA: one Int,
    scoreB: one Int,
    possession: one Team,
    shotClock: one Int,
    event: lone EventType,
    next: lone State
}

// Structural constraints
pred wellformed {
    // Scores can never be negative
    all s: State | {
        s.scoreA >= 0
        s.scoreB >= 0
    }

    // NBA shot clocks are always between 0 and 24 seconds
    all s: State | {
        s.shotClock >= 0
        s.shotClock <= 24
    }

    // States are linear with at most one successor
    all s: State | lone s.next

    // No self loops of states
    all s: State | s.next != s
}

// State transition rules
pred validTransition[s1, s2: State] {
    some s1.event

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
}

// Ensure states have valid transitions
pred transitions {
    all s: State | {
        some s.next => validTransition[s, s.next]
    }
}

// A team needs to have had a possession at some point to have a score greater than 0
pred noScoreWithoutPossession {
    all s: State | {
        s.scoreA > 0 => (some t: State | t.possession = TeamA)
        s.scoreB > 0 => (some t: State | t.possession = TeamB)
    }
}


// If the score changes, there needs to be a ShotMade event
pred scoreOnlyOnMadeShot {
    all s1: State | some s1.next => {
        let s2 = s1.next | (s2.scoreA != s1.scoreA or s2.scoreB != s1.scoreB) =>
            s1.event = ShotMade2 or s1.event = ShotMade3
    }
}

// Run command
run {
    wellformed
    transitions
    scoreOnlyOnMadeShot
} for 5 State, 6 Int