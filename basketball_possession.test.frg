#lang forge/froglet

option bitwidth 6

open "basketball_possession.frg"

one sig TestState extends State {}
one sig TestGame extends Game {}

fact TestSetup {
    TestGame.firstState = TestState
    no TestGame.next
}

test suite for exampleTrace {

    ExampleSat:
        assert init[TestGame.firstState] is sat

}