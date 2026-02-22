#lang forge/froglet

open "basketball_possession.frg"

// Instances
inst validStart {
    State = `S0 + `S1
    Team = `TeamA + `TeamB
    TeamA = `TeamA
    TeamB = `TeamB
    
    EventType = `ShotMade2 + `ShotMade3 + `ShotMissed + `Turnover + `Foul + 
                `OffensiveRebound + `DefensiveRebound + `ShotClockViolation + `GameEnd
    ShotMade2 = `ShotMade2
    ShotMade3 = `ShotMade3
    ShotMissed = `ShotMissed
    Turnover = `Turnover
    Foul = `Foul
    OffensiveRebound = `OffensiveRebound
    DefensiveRebound = `DefensiveRebound
    ShotClockViolation = `ShotClockViolation
    GameEnd = `GameEnd
    
    Game = `G0
    firstState = `G0 -> `S0
    next = `G0 -> `S0 -> `S1

    scoreA = `S0 -> 0 + `S1 -> 2
    scoreB = `S0 -> 0 + `S1 -> 0
    shotClock = `S0 -> 24 + `S1 -> 24
    possession = `S0 -> `TeamA + `S1 -> `TeamB
    event = `S0 -> `ShotMade2 + `S1 -> `GameEnd
}

// Test suite
test suite for wellformed {
    test expect {
        // Make sure to pass the scope (6 Int)
        wf_valid_example: {
            some s0, s1: State | {
                init[s0]
                Game.firstState = s0
                Game.next[s0] = s1
                s1.scoreA = 2
                s1.shotClock = 24
                wellformed
            }
        } for 6 Int is sat
        
        // Testing boundaries without an inst is often cleaner
        wf_clock_limit: {some s: State | s.shotClock = 25 and wellformed} for 6 Int is unsat
    }
}

test suite for gameFlow {
    test expect {
        // Violation must have clock 0
        flow_violation_clock_zero: {
            some s: State | {
                s.event = ShotClockViolation
                s.shotClock = 24
            }
            gameFlow
        } for 6 Int is unsat

        // Final state must be GameEnd
        flow_terminal_game_end: {
            some s: State | no Game.next[s] and s.event = ShotMade2
            gameFlow
        } for 5 State, 6 Int is unsat
    }
}

test suite for validTransition {
    test expect {
        // Missed shot should decrement clock by 1
        trans_miss_decrement: {
            some s1, s2: State | {
                s1.event = ShotMissed
                s1.shotClock = 24
                validTransition[s1, s2]
                s2.shotClock = 23
            }
        } for 6 Int is sat
    }
}