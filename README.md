# curiosity-modeling

Note: We have defined the meanings of the different EventTypes at the bottom section titled Basketball
Terminology Simplified:

1) Project Objective: Our group’s midterm project is trying to model an NBA possession/scoring model, 
showing how a basketball game evolves from one possession to another. The goal of this model is to
demonstrate how different aspects in a basketball game are altered from events that occur during live play
Both of us are huge NBA and basketball fans, spending hours playing in the OMAC gym during our free time. In
addition, we both play intramural basketball together and so we thought it would be both intriguing and
interesting to model something that we were especially enthusiastic about. 

To ensure that both of us learn something meaningful from this project, we centered the scope around
preserving valid transitions from one possession (state) to another and maintaining a realistic flow of the 
game. Furthermore, we focused on the most important characteristics and rules of basketball instead of every 
single technicality. This includes modeling changes to scores, possessions, and the shot clock (which is set 
to a standard 24 seconds at the start of a new possession in the NBA). These changes are influenced by 
certain event types including made two-point baskets, made three-point baskets, missed shots, turnovers, 
fouls, offensive rebounds, defensive rebounds, and violations to the shot clock. At a level that is possible 
to implement, our model has a certain set of constraints to ensure that the rules of basketball are followed 
properly. This involves including only two distinct teams, having a shot clock that adheres to NBA 
regulations (reset to 24 seconds for a new possession and 14 seconds after offensive rebounds and “on the 
floor” fouls), having scores that are only updated in increments of two or three points, allowing for 
possessions to change under the correct situations, and both rebounds and shot clock violations taking place 
in a logical manner. Altogether, our NBA possession and scoring consistency model utilizes Froglet to 
simulate and test the transition from one play to another.


2) Model Design and Visualization: In regards to our model’s design choices, there are five predicates that 
contain all of the logic. Before these predicates are defined in the model, we represented the basketball 
game as a series of State objects, where each state is connected by the function Game.next. Each of these 
states contains the scores for both TeamA and TeamB,  the possession of the team, the time remaining on the 
shot clock, and the event type that occurs during the state. These five predicates will be explained in 
further detail in the next section, but it is worthy to note that all of these predicates include several 
checks and constraints that adhere to the rules of basketball. The fifth predicate is called traces and it 
calls on the other four predicates to ensure that the model is well formed, that it is initialized correctly, 
that the transitions from one state to another follow a logical ordering, and that the game flows in a 
realistic manner. Some checks we would like to highlight is that there are only two teams (and thus two 
scores) at all times, the shot clock time is set at a minimum of 0 seconds (in which case it resets with a 
violation) and a maximum of 24 seconds, and at the start of a game, both teams have a score of 0 and the shot 
clock is set to 24 seconds. In addition to this, the starting state cannot be a rebound or violation. The 
possession changes on turnovers, made shots, defensive rebounds, and shot clock violations, and the 
possession remains the same during missed shots (as this is before a rebound happens), offensive rebounds, 
and fouls. To simplify our model, only “on the floor” fouls will occur, which do not award free throws. 
Furthermore, we designed our model to ensure rebounds only take place after a missed shot and that in the 
final state the game has ended. When running our model, it will generate a valid game sequence of up to 5 
possessions (states) while using 6-bit integers to represent the numbers (due to the necessity to represent 
numbers up to 24 for the shot clock).

From the Sterling visualizer, you can expect to see a jumble of states, values, and transitions. Due to how 
many things we are modeling, the visualizer itself is quite hard to interpret. Thus, to best interpret an 
instance created by our spec, one should use the “Table” tab instead. This table will display all of the 
necessary pieces of information. We would recommend looking at the table in this order: consider what happens 
in each state in “event”, ensure the shot clock is possible for each state in “shotClock”, ensure the chain 
of team possessions in “possession” is correct given each state, and finally, ensure the scores for both 
teams are as expected in each state. Overall, we used the default layout.cnd to help visualize the game in a 
chronological manner, allowing us to track the development of the game from beginning to end.


3) Signatures and Predicates: At a high level, we had several signatures and predicates used throughout our 
model. To begin with, we used an abstract signature called Team, in which we also created one signature 
called TeamA and one signature called TeamB that extends the Team signature. This made it so that the only 
Teams that could exist in our model were these two particular teams. Similarly, we used an abstract signature 
called EventType, in which we also created a variety of different signatures that extend EventType. These 
signatures that extend EventType demonstrate all the different events that can occur during the possession 
model, and vary from ShotMade2, ShotMade3, ShotMissed, Turnover, Foul, OffensiveRebound, DefensiveRebound, 
ShotClockViolation, and GameEnd (these are defined in more detail at the bottom of README). There is also the 
State signature, which represents what potentially occurs during each state of the game. This signature 
assigns an Integer value to the scores and shot clock variables, a Team to the possession variable, and an 
EventType to the event variable. Finally, there is the Game signature that contains the first state and the 
logic for the next state that enables state transitions. 

We have five predicates. The predicate called wellformed represents property constraints for the model and 
ensures that for all states, both scores can never be negative and that the model adheres to the NBA shot 
clock system. The wellformed predicate also makes sure that no state can come before the first state. Next, 
the init predicate sets constraints for the initial state. It ensures that the scores start from 0, the shot 
clock starts at 24 seconds, and prevents impossible events from occurring in the first state. Our largest 
predicate is called validTransition, and it defines the rules of basketball for each state and updates 
changes to the score, possession, and clock based on events. For instance, for made shots, the respective 
scores are updated, the possession changes, and the shot clock is reset to 24 seconds. For missed shots, both 
scores and the possession remain the same, but 1 second is taken off from the shot clock (just to account for 
the time of the ball in the air). For turnovers, while the scores do not change, the possession does, and the 
clock is reset. For both fouls and offensive rebounds, the scores and possession stay the same, but in the 
case that the shot clock is under 14 seconds, the clock is reset back to 14 seconds per NBA regulations. 
Alternatively, defensive rebounds change possession but do not impact scores and allow the shot clock to 
reset back to 24 seconds. Finally, a shot clock violation occurs when there are 0 seconds left on the clock, 
flipping the possession without impacting scores and resetting the shot clock back to 24 seconds. The next 
predicate is gameFlow, which ensures that the game flows smoothly and realistically. This includes logical 
implications such as clock violations only occurring during 0 seconds, rebounds following missed shots, score 
updates following made shots, and viable endings for games. The final predicate is called traces, and it 
simply ensures that a game can be run properly with all the previously defined predicates.


4) Testing: Several tests were written to test our model. We used a combination of test expects and assert 
statements to verify the properties of our domain area. We wrote five different test suites, with there being 
one per respective predicate. In regards to testing our model itself, we created suites surrounding the 
wellformed, init, and traces predicates. These tests ensure that the model works as expected with 6-bit 
integers, which we initially had issues with due to the 24 seconds shot clock (was out of bounds in the 
default range of 4-bit integers from -7 to 8). Additionally, to further test our model within these three 
predicates, we checked that they were either satisfactory or unsatisfactory (for edge cases). For example in 
the wellformed test suite, we checked that the value of the shot clock remained within 0 and 24 seconds, that 
there is always a first state when wellformed is called, that the first state has no predecessor, that every 
state has a next state at the maximum, that the shot clock cannot be greater than 24 seconds or negative, and 
that neither of the teams can have negative scores at any point during the game. For the init test suite, we 
primarily ensured that scores and shot clock were reset properly to their normal values and that the game 
starts on a valid event type. For the traces test suite, we made sure that this predicate could coexist with 
the other predicates by ensuring that a valid trace could occur after a valid transition or a wellformed 
game. Seeing all of these extensive tests pass allowed us to verify the validity of our model.

In regards to testing properties of our domain area, we created suites surrounding the validTransition and 
gameFlow predicates. These tests helped verify that all of the rules of basketball were being followed 
realistically. We created both possible and impossible scenarios that could take place in a game so that our 
possession and scoring consistency model was as feasible as possible. For instance, in the validTransition 
test suite, we verified that a missed shot decreases the shot clock by exactly one second and that correct 
updates were made to the scores, possession, and shot clock based on different events. For each of these 
event types, we wrote both valid and invalid scenarios that ran correctly when properties were followed 
correctly and intentionally failed when properties were followed incorrectly. We also checked an edge case to 
ensure the scores could not decrease from one state to another. Finally, in the gameFlow test suite, we wrote 
tests checking that a violation only occurs if the shot clock reaches 0, that rebounds must be preceded by a 
missed shot, that a missed shot must be followed by a rebound, that a score change indicates a made shot 
beforehand, and the game ends if there is no next state. It is also noteworthy that we created an instance 
called validStart to instantiate a simple game with only two states to carry out tests.  


5) Documentation: All files related to the model and tests have been well-documented to help better 
understand the structure and logic of our project!


Basketball Terminology Simplified:

ShotMade2: This is a made basket worth two points that is shot from within the 3-point line.
ShotMade3: This is a made basket worth three points that is shot from outside the 3-point line.
ShotMissed: This is a missed shot attempt that fails to enter the basket.
Turnover: This is a turnover where one team loses possession of the ball and thus gives it to the other team.
Foul: This is when a team makes illegal physical contact with the other team.
OffensiveRebound: This is when a team regains possession of the ball after their own missed shot.
DefensiveRebound: This is when a team gains possession of the ball after the other team missed a shot.
ShotClockViolation: This is a violation when a team fails to attempt a shot within 24 seconds.
GameEnd: This signifies that the game has ended. 
