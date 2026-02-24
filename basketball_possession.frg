#lang forge/froglet

// this loads the visualization script
option run_sterling "layout.cnd"

// This is our NBA Possession & Scoring Consistency Model

// This represents the basic game structure
// this creates an abstract sig called Team
abstract sig Team {}
// there exactly two teams that will be used in this model (Team A or Team B)
one sig TeamA, TeamB extends Team {}
// this creates an abstract sig called EventType
abstract sig EventType {}
// this defines all the different events that can occur during the possession model 
one sig ShotMade2, ShotMade3, ShotMissed, Turnover, Foul, OffensiveRebound, DefensiveRebound, ShotClockViolation, GameEnd extends EventType {}

// this represents what potentially occurs during each state of the game 
sig State {
    scoreA: one Int,
    scoreB: one Int,
    possession: one Team,
    shotClock: one Int,
    event: lone EventType
}

// this defines the logic of states during each game
one sig Game {
    firstState: one State,
    next: pfunc State -> State
}

// This represents the structural constraints within the wellformed predicate 
pred wellformed {
    // this ensures that for all states, both scores can never be negative, 
    // and NBA shot clocks are always between 0 and 24 seconds
    all s: State | {
        s.scoreA >= 0
        s.scoreB >= 0
        s.shotClock >= 0
        s.shotClock <= 24
    }
    
    // this makes sure that the first state of the game cannot have any predecessor
    no prev: State | Game.next[prev] = Game.firstState
}

// This is a predicate that initializes the state
pred init[s: State] {
    // all the scores for both teams must be set to zero
    s.scoreA = 0
    s.scoreB = 0
    // the shot clock is reset to 24 seconds (standard time in the NBA)
    s.shotClock = 24

    // the game cannot start in one of the following states
    // the game cannot start on a rebound since a missed shot must occur prior
    s.event != OffensiveRebound
    s.event != DefensiveRebound
    // the game cannot start on a shot clock violation since the shot clock is set to 24 seconds by default
    s.event != ShotClockViolation
}

// This is a predicate that defines the state transition rules
pred validTransition[s1, s2: State] {
    // first define one event for the first state 
    one s1.event

    // Score a 2 pointer
    (s1.event = ShotMade2) => {
        // checks if TeamA scores a two pointer (TeamA has possession)
        (s1.possession = TeamA => {
            // then add 2 to scoreA
            s2.scoreA = add[s1.scoreA, 2]
            // sets the state 2 scoreB to the state 1 scoreB (the same)
            s2.scoreB = s1.scoreB
        })
        
        // checks if TeamB scores a two pointer (TeamB has possession)
        (s1.possession = TeamB => {
            // then add 2 to scoreB
            s2.scoreB = add[s1.scoreB, 2]
            // sets the state 2 scoreA to the state 1 scoreA (the same)
            s2.scoreA = s1.scoreA
        })

        // on a two point make, the possession changes 
        s2.possession != s1.possession
        // the shot clock also resets to 24 seconds 
        s2.shotClock = 24
    }

    // Score a 3 pointer
    (s1.event = ShotMade3) => {
        // checks if TeamA scores a three pointer (TeamA has possession)
        (s1.possession = TeamA => {
            // then add 3 to scoreA
            s2.scoreA = add[s1.scoreA, 3]
            // sets the state 2 scoreB to the state 1 scoreB (the same)
            s2.scoreB = s1.scoreB
        })

        // checks if TeamB scores a three pointer (TeamB has possession)
        (s1.possession = TeamB => {
            // then add 3 to scoreB
            s2.scoreB = add[s1.scoreB, 3]
            // sets the state 2 scoreA to the state 1 scoreA (the same)
            s2.scoreA = s1.scoreA
        })

        // on a three point make, the possession changes 
        s2.possession != s1.possession
        // the shot clock also resets to 24 seconds 
        s2.shotClock = 24
    }

    // If a shot is missed, the scores don't change and there is also no possession 
    // change in case of offensive rebound
    (s1.event = ShotMissed) => {
        // ensures that the scoreA remains the same
        s2.scoreA = s1.scoreA
        // ensures that the scoreB remains the same
        s2.scoreB = s1.scoreB
        // the possession does not change
        s2.possession = s1.possession
        // one second is taken off from the shot clock 
        s2.shotClock = subtract[s1.shotClock, 1]
    }

    // If turnover, scores don't change, but possession changes and shot clock resets
    (s1.event = Turnover) => {
        // ensures that the scoreA remains the same
        s2.scoreA = s1.scoreA
        // ensures that the scoreB remains the same
        s2.scoreB = s1.scoreB
        // the possession does change
        s2.possession != s1.possession
        // the shot clock resets to 24 seconds 
        s2.shotClock = 24
    }

    // To simplify the model, only "on the floor" fouls will happen. These are fouls that do not award free throws.
    (s1.event = Foul) => {
        // ensures that the scoreA and scoreB remains the same
        s2.scoreA = s1.scoreA
        s2.scoreB = s1.scoreB
        // the possession does not change
        s2.possession = s1.possession

        // In the case that the shot clock is under 14 seconds, in the NBA, a foul causes it to reset back to 14 seconds
        (s1.shotClock < 14 => s2.shotClock = 14)
        // but, if the shot clock is over 14 seconds, the time remains as is 
        (s1.shotClock >= 14 => s2.shotClock = s1.shotClock)
    }

    // Offensive rebounds do not change score or possession
    (s1.event = OffensiveRebound) => {
        // ensures that the scoreA and scoreB remains the same
        s2.scoreA = s1.scoreA
        s2.scoreB = s1.scoreB
        // the possession does not change
        s2.possession = s1.possession

        // In the case that the shot clock is under 14 seconds, in the NBA, an offensive rebound causes it to reset back to 14 seconds
        (s1.shotClock < 14 => s2.shotClock = 14)
        // but, if the shot clock is over 14 seconds, the time remains as is 
        (s1.shotClock >= 14 => s2.shotClock = s1.shotClock)
    }

    // Defensive rebounds do not change score but change possession and reset shot clock
    (s1.event = DefensiveRebound) => {
        // ensures that the scoreA and scoreB remains the same
        s2.scoreA = s1.scoreA
        s2.scoreB = s1.scoreB
        // the possession does change
        s2.possession != s1.possession
        // the shot clock thus resets to 24 seconds 
        s2.shotClock = 24
    }

    // Shot clock violation (clock reaches 0) flips the possession
    (s1.event = ShotClockViolation) => {
        // the shot clock is set to zero seconds 
        s1.shotClock = 0
        // ensures that the scoreA and scoreB remains the same
        s2.scoreA = s1.scoreA
        s2.scoreB = s1.scoreB
        // the possession does change
        s2.possession != s1.possession
        // the shot clock thus resets to 24 seconds 
        s2.shotClock = 24
    }
}

// This is the predicate that ensures that the game flows smoothly and realistically
pred gameFlow {
    all s: State | {
        // here a violation can only exist if the shot clock is at 0
        (s.event = ShotClockViolation) <=> (s.shotClock = 0)
        
        // both types of rebounds must be preceded by a missed shot
        (s.event = OffensiveRebound or s.event = DefensiveRebound) implies {
            some prev: State | Game.next[prev] = s and prev.event = ShotMissed
        }
        
        // also, missed shots have to be followed by a rebound
        (s.event = ShotMissed) implies {
            some nxt: State | Game.next[s] = nxt and (nxt.event = OffensiveRebound or nxt.event = DefensiveRebound)
        }

        // if the score changes, then this means that there needs to be a ShotMade event (two or three pointer)
        (some prev: State | Game.next[prev] = s and (s.scoreA != prev.scoreA or s.scoreB != prev.scoreB)) implies {
            all prev: State | Game.next[prev] = s implies (prev.event = ShotMade2 or prev.event = ShotMade3)
        }

        // finally, if there is no next state, then this means that the game ends
        (no Game.next[s]) <=> s.event = GameEnd
    }
}

// This is the traces predicate which ensures that a game can be run properly with all the previously defined predicates
pred traces {
    // calls the wellformed predicate 
    wellformed
    // calls the init predicate on the first state of the game 
    init[Game.firstState]
    // for all states, there is some valid transition that takes place from one state to another 
    all s: State | some Game.next[s] implies validTransition[s, Game.next[s]]
    // finally calls the game flow predicate 
    gameFlow
}

// this is the run command which calls traces for 5 states and 6 Ints. It also uses the next is linear logic
run {
    traces
} for 5 State, 6 Int for { next is linear }