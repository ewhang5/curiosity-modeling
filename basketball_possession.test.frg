#lang forge/froglet

open "basketball_possession.frg"

// this instantiates a simple game with only two states in order to carry out tests 
inst validStart {
    // constrains this to two states
    State = `State0 + `State1
    // also instantiates the two teams that will be represented which is the Lakers and Clippers (TeamA and TeamB)
    Team = `Lakers + `Clippers
    TeamA = `Lakers
    TeamB = `Clippers
    // here we set all the event types that are possible (we created this in basketball_possession.frg in the same order)
    EventType = `ShotMade2 + `ShotMade3 + `ShotMissed + `Turnover + `Foul + 
                `OffensiveRebound + `DefensiveRebound + `ShotClockViolation + `GameEnd
    // here each event type includes one thing (which is specific to that respective event)   
    // this defines a shot that is worth 2 points         
    ShotMade2 = `ShotMade2
    // this defines a shot that is worth 3 points         
    ShotMade3 = `ShotMade3
    // this defines a missed shot worth 0 points 
    ShotMissed = `ShotMissed
    // this defines a turnover when a team loses possession of a ball 
    Turnover = `Turnover
    // this defines a foul when a player makes illegal physical contact with another player 
    Foul = `Foul
    // this defines an offensive rebound where a team maintains possession after a missed shot
    OffensiveRebound = `OffensiveRebound
    // this defines a defensive rebound where a team loses possession after a missed shot
    DefensiveRebound = `DefensiveRebound
    // this defines a shot clock violation where a time spends over 24 seconds on a possession
    ShotClockViolation = `ShotClockViolation
    // this defines the ending of a game
    GameEnd = `GameEnd
    // this defines the first and second states of the game
    Game = `Game0
    firstState = `Game0 -> `State0
    next = `Game0 -> `State0 -> `State1
    // this defines different scoreing scenarios from the two teams
    scoreA = `State0 -> 0 + `State1 -> 2
    scoreB = `State0 -> 0 + `State1 -> 0
    // this sets the shotclock for both states
    shotClock = `State0 -> 24 + `State1 -> 24
    // this defines the possessions for each state 
    possession = `State0 -> `Lakers + `State1 -> `Clippers
    // this defines the events that occur 
    event = `State0 -> `ShotMade2 + `State1 -> `GameEnd
}

// this is a test suit for the wellformed predicate
test suite for wellformed {
    
    // uses the test expect notaiton in this instance 
    test expect {
        // this test ensures to model passes the scope of 6 Ints
        valid_wellformed: {
            // for some State0 and State 1
            some State0, State1: State | {
                // this makes State0 a valid initial state 
                init[State0]
                // sets the first state to State0 and the next state to State1
                Game.firstState = State0
                Game.next[State0] = State1
                // sets the score and shot clock during State1
                State1.scoreA = 4
                State1.shotClock = 24
                // calls wellformed
                wellformed
            }
        // ensures that this is suitable for 6 integers (since dealing with shotclock of 24 seconds)    
        } for 6 Int is sat
        
        // these tests ensures that the value of the shotclock must stay within 0 and 24 seconds 
        invalid_clock: {
            some state1: State | state1.shotClock = 25 and wellformed} for 6 Int is unsat  
        valid_clock1: {
            some state2: State | state2.shotClock = 23 and wellformed} for 6 Int is sat
        valid_clock2: {
            some state3: State | state3.shotClock = 8 and wellformed} for 6 Int is sat
    }

    // now here is a series of assert of statements of different scenarios where wellformed is satisfied or unsatisfied
    // also accounts for the integer scope
    valid_wellform: assert wellformed is sat for 5 State, 6 Int

    // this ensures that there is always a first state when wellformed is called 
    valid_first_state: assert wellformed implies one Game.firstState is sat for 5 State, 6 Int

    // this ensures that the first state has no predecessor
    pred_state: assert {some predState: State | Game.next[predState] = Game.firstState } is inconsistent with wellformed for 5 State, 6 Int

    // this checks to make sure that every state has a next state at the maximum (can have at most 1 next state)
    nextmax_state: assert {wellformed implies (all nextstate: State | lone nextstate.(Game.next))} is sat for 5 State, 6 Int

    // these tests ensure that the shot clock cannot be greater than 24 seconds 
    more_twentyfour1: assert {some clock: State | clock.shotClock = 31} is inconsistent with wellformed for 5 State, 6 Int
    more_twentyfour2: assert {some clock: State | clock.shotClock = 28} is inconsistent with wellformed for 5 State, 6 Int

    // these assert statements maintain the fact that the value of the clock cannot be a negative time
    less_twentyfour1: assert {some nstate: State | nstate.shotClock = -5} is inconsistent with wellformed for 5 State, 6 Int
    less_twentyfour2: assert {some negstate: State | negstate.shotClock < 0} is inconsistent with wellformed for 5 State, 6 Int

    // these tests check that neither of the teams can have negative scores at any point during the game 
    negative_score1: assert {some nscore1: State | nscore1.scoreA < 0} is inconsistent with wellformed for 5 State, 6 Int
    negative_score2: assert {some nscore2: State | nscore2.scoreB = -1} is inconsistent with wellformed for 5 State, 6 Int
}

// this is a test suit for the gameFlow predicate
test suite for gameFlow {

    // uses the test expect notaiton in this instance 
    test expect {
        // ensures that the last state properly ends the game
        game_ending: {
            // declares an end state to end the game
            some endstate: State | no Game.next[endstate] and endstate.event = ShotMade2
            gameFlow
        } for 5 State, 6 Int is unsat

        // here a shotclock violation should reset the time correctly
        shot_clock_violation: {
            // for some State0 and State 1
            some state1: State | {
                // calls the ShotClockViolation
                state1.event = ShotClockViolation
                // sets the shotclock back to 24 seconds
                state1.shotClock = 24
            }
            // calls gameFlow
            gameFlow
        // ensures that this is suitable for 6 integers (since dealing with shotclock of 24 seconds)        
        } for 6 Int is unsat
    }
}

// this is a test suit for the validTransition predicate
test suite for validTransition {

    // uses the test expect notaiton in this instance 
    test expect {
        // here a missed shot decreases the shotclock by 1 (reasonable)
        clock_decrease_valid: {
            // for same State1 and State2
            some State1, State2: State | {
                // a shot is missed in State1
                State1.event = ShotMissed
                // the clock is set to 24 seconds
                State1.shotClock = 24
                // a valid transition occurs which in turn reduces the shotclock by 1 second
                validTransition[State1, State2]
                State2.shotClock = 23
            }
        // ensures that this is suitable for 6 integers (since dealing with shotclock of 24 seconds)    
        } for 6 Int is sat

        // here a missed shot decreases the shotclock by 2 second which is invalid
        clock_decrease_invalid: {
            // for same State1 and State2
            some State1, State2: State | {
                // a shot is missed in State1
                State1.event = ShotMissed
                // the clock is set to 24 seconds
                State1.shotClock = 24
                // a valid transition occurs
                validTransition[State1, State2]
                // the shotclock is reduced by 2 seconds which results in unsat
                State2.shotClock = 22
            }
        // ensures that this is suitable for 6 integers (since dealing with shotclock of 24 seconds)    
        } for 6 Int is unsat
    }

}

