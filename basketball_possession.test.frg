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
test suite for init {

    // uses the test expect notaiton in this instance 
    test expect {
        // this checks that some initState is a valid initial state 
        valid_init: {some initState: State | init[initState]} for 5 State, 6 Int is sat     
        // this checks when the score and shotclock are reset properly to their normal values
        init_score1: {some initState: State | init[initState] and initState.scoreA = 0 and initState.scoreB = 0} 
            for 5 State, 6 Int is sat  
        init_clock1: {some initState: State | init[initState] and initState.shotClock = 24} 
            for 5 State, 6 Int is sat 
        // this checks when the score and shotclock are not reset properly to their normal values
        init_score2: {some initState: State | init[initState] and initState.scoreA = 12 and initState.scoreB = 7} 
            for 5 State, 6 Int is unsat  
        init_clock2: {some initState: State | init[initState] and initState.shotClock = 19} 
            for 5 State, 6 Int is unsat 
    }
    
    // now here is a series of assert of statements of different scenarios where init is satisfied or unsatisfied
    // this test ensures that the game does not start on an OffensiveRebound
    invalid_start1: assert {some initState: State | init[initState] and initState.event = OffensiveRebound} is unsat for 5 State, 6 Int
    // this test ensures that the game does not start on a DefensiveRebound
    invalid_start2: assert {some initState: State | init[initState] and initState.event = DefensiveRebound} is unsat for 5 State, 6 Int
    // this test ensures that the game does not start on an ShotClockViolation
    invalid_start3: assert {some initState: State | init[initState] and initState.event = ShotClockViolation} is unsat for 5 State, 6 Int
    // these test prove that the game can start on vali events that are not shot clock violations or rebounds
    valid_init1: assert {some initState: State | init[initState] and initState.event = Foul} is sat for 5 State, 6 Int
    valid_init2: assert {some initState: State | init[initState] and initState.event = ShotMissed} is sat for 5 State, 6 Int
    valid_init3: assert {some initState: State | init[initState] and initState.event = Turnover} is sat for 5 State, 6 Int
    valid_init4: assert {some initState: State | init[initState] and initState.event = ShotMade3} is sat for 5 State, 6 Int
    valid_init5: assert {some initState: State | init[initState] and initState.event != GameEnd} is sat for 5 State, 6 Int
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
                // the scores remain the same
                State2.scoreA = State1.scoreA
                State2.scoreB = State1.scoreB
                // the posssession also remains the same (in case of offensive rebound)
                State2.possession = State1.possession
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

    // now here is a series of assert of statements of different scenarios where wellforvalid transition is satisfied or unsatisfied
    // first just a basic check to ensure it is satisfiable between two different states 
    valid_trans: assert {some state1, state2: State | validTransition[state1, state2]} is sat for 5 State, 6 Int
    // if a 2 pointer is made, check for teamB and make sure shot clock resets and possession changes
    validA_twopointerB: assert all state1, state2: State | validTransition[state1, state2] and state1.event = ShotMade2
        and state1.possession = TeamB implies (state2.scoreB = add[state1.scoreB, 2] and state2.scoreA = state1.scoreA and 
        state2.shotClock = 24 and state2.possession = TeamA) is sat for 5 State, 6 Int 
    // if a 2 pointer is made, check for teamA and make sure shot clock resets and possession changes
    validA_twopointerA: assert all state1, state2: State | validTransition[state1, state2] and state1.event = ShotMade2
        and state1.possession = TeamA implies (state2.scoreA = add[state1.scoreA, 2] and state2.scoreB = state1.scoreB and 
        state2.shotClock = 24 and state2.possession = TeamB) is sat for 5 State, 6 Int 
    // checks an invalid 2 pointer where more than 2 points is added and the shotclock does not reset 
    invalidA_twopointer1: assert all state1, state2: State | validTransition[state1, state2] and state1.event = ShotMade2
        and state1.possession = TeamB and state2.scoreB = add[state1.scoreB, 4] and state2.scoreA = state1.scoreA and 
        state2.shotClock = 18 and state2.possession = TeamA is unsat for 5 State, 6 Int 
    // checks an invalid 2 pointer where the possession does not change
    invalidA_twopointer2: assert all state1, state2: State | validTransition[state1, state2] and state1.event = ShotMade2
        and state1.possession = TeamB and state2.scoreB = add[state1.scoreB, 2] and state2.scoreA = state1.scoreA and 
        state2.shotClock = 24 and state2.possession = TeamB is unsat for 5 State, 6 Int 

    // if a 3 pointer is made, check for teamB and make sure shot clock resets and possession changes
    validA_threepointerB: assert all state1, state2: State | validTransition[state1, state2] and state1.event = ShotMade3
        and state1.possession = TeamB implies (state2.scoreB = add[state1.scoreB, 3] and state2.scoreA = state1.scoreA and 
        state2.shotClock = 24 and state2.possession = TeamA) is sat for 5 State, 6 Int 
    // if a 2 pointer is made, check for teamA and make sure shot clock resets and possession changes
    validA_threepointerA: assert all state1, state2: State | validTransition[state1, state2] and state1.event = ShotMade3
        and state1.possession = TeamA implies (state2.scoreA = add[state1.scoreA, 3] and state2.scoreB = state1.scoreB and 
        state2.shotClock = 24 and state2.possession = TeamB) is sat for 5 State, 6 Int 
    // checks an invalid 2 pointer where more than 2 points is added and the shotclock does not reset 
    invalidA_threepointer1: assert all state1, state2: State | validTransition[state1, state2] and state1.event = ShotMade3
        and state1.possession = TeamA and state2.scoreA = add[state1.scoreA, 4] and state2.scoreB = state1.scoreB and 
        state2.shotClock = 16 and state2.possession = TeamB is unsat for 5 State, 6 Int 
    // checks an invalid 2 pointer where the possession does not change
    invalidA_threepointer2: assert all state1, state2: State | validTransition[state1, state2] and state1.event = ShotMade3
        and state1.possession = TeamA and state2.scoreA = add[state1.scoreA, 3] and state2.scoreB = state1.scoreB and 
        state2.shotClock = 24 and state2.possession = TeamA is unsat for 5 State, 6 Int 
    
    // if a turnover occurs, then the shot clock resets and the possession changes
    valid_turnover: assert all state1, state2: State | validTransition[state1, state2] and state1.event = Turnover
        implies (state2.shotClock = 24 and state1.possession != state2.possession and state2.scoreB = state1.scoreB and
        state2.scoreA = state1.scoreA) is sat for 5 State, 6 Int 
    // invalid turnover where the possession does not change 
    invalid_turnover1: assert all state1, state2: State | validTransition[state1, state2] and state1.event = Turnover
        and state2.shotClock = 24 and state1.possession = state2.possession and state2.scoreB = state1.scoreB and
        state2.scoreA = state1.scoreA is unsat for 5 State, 6 Int 
    // invalid turnover where the shot clock does not reset correctly
    invalid_turnover2: assert all state1, state2: State | validTransition[state1, state2] and state1.event = Turnover
        and state2.shotClock = 5 and state1.possession != state2.possession and state2.scoreB = state1.scoreB and
        state2.scoreA = state1.scoreA is unsat for 5 State, 6 Int 

    // this tests that if a foul occurs, then the score and possession stays the same 
    valid_foul: assert all state1, state2: State | validTransition[state1, state2] and state1.event = Foul
        implies (state2.shotClock = 24 and state1.possession = state2.possession and state2.scoreB = state1.scoreB and
        state2.scoreA = state1.scoreA) is sat for 5 State, 6 Int 
    // invalid foul where the possession does not change 
    invalid_foul1: assert all state1, state2: State | validTransition[state1, state2] and state1.event = Foul
        and state2.shotClock = 24 and state2.possession != state1.possession and state2.scoreB = state1.scoreB and
        state2.scoreA = state1.scoreA is unsat for 5 State, 6 Int 
    // invalid foul where the shot clock does not reset correctly
    invalid_foul2: assert all state1, state2: State | validTransition[state1, state2] and state1.event = Foul
        and state2.shotClock = 7 and state1.possession = state2.possession and state2.scoreB = state1.scoreB and
        state2.scoreA = state1.scoreA is unsat for 5 State, 6 Int 
    // for fouls, if shotclock is under 14 seconds then the shotclock is reset to 14 
    foul_clock: assert all state1, state2: State | validTransition[state1, state2] and state1.event = Foul 
        and state1.shotClock = 3 implies state1.possession = state2.possession and state2.shotClock = 14 
        is sat for 5 State, 6 Int 

    // offensive boards maintain score and possession
    valid_oboard: assert all state1, state2: State | validTransition[state1, state2] and state1.event = OffensiveRebound
        implies (state1.possession = state2.possession and state2.scoreB = state1.scoreB and state2.scoreA = state1.scoreA) 
        is sat for 5 State, 6 Int 
    // invalid offensive rebound where the possession changes
    invalid_oboard1: assert all state1, state2: State | validTransition[state1, state2] and state1.event = OffensiveRebound
        and state1.possession != state2.possession and state2.scoreB = state1.scoreB and state2.scoreA = state1.scoreA
        is unsat for 5 State, 6 Int 
    // invalid offensive rebound where the scores do not stay the same 
    invalid_oboard2: assert all state1, state2: State | validTransition[state1, state2] and state1.event = OffensiveRebound
        and state1.possession = state2.possession and state2.scoreB != state1.scoreB and state2.scoreA != state1.scoreA
        is unsat for 5 State, 6 Int 
    // for offensive rebounds, if shotclock is under 14 seconds then the shotclock is reset to 14 
    or_clock1: assert all state1, state2: State | validTransition[state1, state2] and state1.event = OffensiveRebound 
        and state1.shotClock = 12 implies state1.possession = state2.possession and state2.shotClock = 14 
        is sat for 5 State, 6 Int 
    or_clock2: assert all state1, state2: State | validTransition[state1, state2] and state1.event = OffensiveRebound 
        and state1.shotClock = 15 implies state1.possession = state2.possession and state2.shotClock = 15 
        is sat for 5 State, 6 Int 

    // defensive rebounds do not change score, but change possession and reset shotclock
    valid_dboard: assert all state1, state2: State | validTransition[state1, state2] and state1.event = DefensiveRebound
        implies (state2.shotClock = 24 and state1.possession != state2.possession and state2.scoreB = state1.scoreB and state2.scoreA = state1.scoreA) 
        is sat for 5 State, 6 Int 
    // invalid defensive rebound where the scores change
    invalid_dboard1: assert all state1, state2: State | validTransition[state1, state2] and state1.event = DefensiveRebound
        and state2.shotClock = 24 and state1.possession != state2.possession and state2.scoreB = add[state1.scoreB, 4] 
        and state2.scoreA = state1.scoreA is unsat for 5 State, 6 Int 
    // invalid offensive rebound where the possession does not change
    invalid_dboard2: assert all state1, state2: State | validTransition[state1, state2] and state1.event = DefensiveRebound
        and state2.shotClock = 24 and state1.possession = state2.possession and state2.scoreB = state1.scoreB and 
        state2.scoreA = state1.scoreA is unsat for 5 State, 6 Int 
    // for defensive rebounds, the shotclock resets to 24 seconds 
    dr_clock: assert all state1, state2: State | validTransition[state1, state2] and state1.event = DefensiveRebound 
        and state1.shotClock = 12 implies state1.possession = state2.possession and state2.shotClock = 24 
        is sat for 5 State, 6 Int 
   
    // a shotclock violation switches possession, keeps scores the same, and resets the clock as well
    valid_violation: assert all state1, state2: State | validTransition[state1, state2] and state1.event = ShotClockViolation and state1.shotClock = 0
        implies (state2.shotClock = 24 and state1.possession != state2.possession and state2.scoreB = state1.scoreB and state2.scoreA = state1.scoreA) 
        is sat for 5 State, 6 Int 
    // invalid violation where the scores change 
    invalid_violation1: assert all state1, state2: State | validTransition[state1, state2] and state1.event = ShotClockViolation
        and state2.shotClock = 24 and state1.possession != state2.possession and state2.scoreB = add[state1.scoreB, 3] 
        and state2.scoreA = state1.scoreA is unsat for 5 State, 6 Int 
    // invalid violation where the possession does not change
    invalid_violation2: assert all state1, state2: State | validTransition[state1, state2] and state1.event = ShotClockViolation
        and state2.shotClock = 24 and state1.possession = state2.possession and state2.scoreB = state1.scoreB and 
        state2.scoreA = state1.scoreA is unsat for 5 State, 6 Int 
    // invalid reset if the shotclock does not actually hit 0 
    violation_clock: assert all state1, state2: State | validTransition[state1, state2] and state1.event = ShotClockViolation 
        and state1.shotClock = 1 and state1.possession = state2.possession and state2.shotClock = 24 
        is unsat for 5 State, 6 Int 

    // tests an edge case where the scores cannot decrease from one state to another 
    invalid_scoring: assert all state1, state2: State | validTransition[state1, state2] 
        and state2.scoreB < state1.scoreB and state2.scoreA < state1.scoreA is unsat for 5 State, 6 Int
}

// this is a test suit for the gameFlow predicate
test suite for gameFlow {

    // uses the test expect notaiton in this instance 
    test expect {
        // does an invalid check that the last state properly ends the game
        game_ending: {
            // does not declare an end state to end the game
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

    // now here is a series of assert of statements of different scenarios where game flow is satisfied or unsatisfied
    // this first check ensures that a violation only occurs if the shotclock reaches 0
    valid_gf: assert all state1, state2: State | gameFlow and Game.next[state1] = state2 and 
        state1.event = ShotClockViolation implies state1.shotClock = 0 is sat for 5 State, 6 Int 
    // this is a invalid game flow where the shotclock does not yet reach 0 
    invalid_gf: assert all state1, state2: State | gameFlow and Game.next[state1] = state2 and 
        state1.event = ShotClockViolation and state1.shotClock = 16 is unsat for 5 State, 6 Int 
    // this check ensures that rebounds must be preceded by a missed shot
    valid_gfreb: assert all state1, state2: State | gameFlow and Game.next[state1] = state2 and 
        state2.event = DefensiveRebound implies state1.event = ShotMissed is sat for 5 State, 6 Int 
    // this is is an invalid game flow where a rebound is not preceded by a missed shot
    invalid_gfreb: assert all state1, state2: State | gameFlow and Game.next[state1] = state2 and 
        state2.event = DefensiveRebound and state1.event = ShotMade2 is unsat for 5 State, 6 Int 
    // this ensures that a missed shot must be followed by a rebound from one event to another 
    gf_miss1: assert all state1, state2: State | gameFlow and Game.next[state1] = state2 and 
        state1.event = ShotMissed and state2.event = Turnover is unsat for 5 State, 6 Int 
    gf_miss2: assert all state1, state2: State | gameFlow and Game.next[state1] = state2 and 
        state1.event = ShotMissed and state2.event = Foul is unsat for 5 State, 6 Int 
    // this ensures that if the score changes, there needs to be a ShotMade event
    gf_scorechange1: assert all state1, state2: State | gameFlow and Game.next[state1] = state2 and 
        state1.event = ShotMissed and state2.scoreA = add[state1.scoreA, 2] is unsat for 5 State, 6 Int 
    gf_scorechange2: assert all state1, state2: State | gameFlow and Game.next[state1] = state2 and 
        state1.event = OffensiveRebound and state2.scoreB = add[state1.scoreB, 3] is unsat for 5 State, 6 Int 
    // finally this ensures that if there is no next state, the game ends
    gf_over: assert all state1, state2: State | gameFlow and Game.next[state1] != state2 and 
        state1.event = GameEnd is sat for 5 State, 6 Int 
}

// this is a test suite for the traces predicate
test suite for traces {
// primarily used assert test for this predicate as well
    // this is basic check to ensure that traces is satisfiable for the current integer bound
    valid_trace: assert traces is sat for 5 State, 6 Int
    // this ensures that a trace is valid after validTransitions take place 
    transition_trace: assert {some firstState, secondState: State | 
        traces and validTransition[firstState, secondState]} is sat for 5 State, 6 Int
    // this ensures that a trace is valid after validTransitions take place with two states in a row
    consec_trace: assert {some firstState, secondState: State | 
        traces and Game.next[firstState] = secondState and validTransition[firstState, secondState]} 
        is sat for 5 State, 6 Int
    // this checks an unsatisfactory case when there is not a valid transition that takes place between two states
    invalid_trace: assert {some firstState, secondState: State | 
        traces and Game.next[firstState] = secondState and not validTransition[firstState, secondState]} 
        is unsat for 5 State, 6 Int
    // this checks that traces can be satisfied with a wellformed game
    wellformed_traces: assert traces implies wellformed is sat for 5 State, 6 Int 
    // this checks that for a game that is well traced, the game ends correctly
    ending_trace: assert {some firstState, secondState: State | 
        traces and no Game.next[secondState] and secondState.event = GameEnd} 
        is sat for 5 State, 6 Int
}