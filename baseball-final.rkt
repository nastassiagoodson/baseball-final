#lang forge
--a sig defining players
sig Player {
  next : one Player
}

--there should be 9 players (Rule 5.02)
one sig Player0 extends Player{}
one sig Player1 extends Player{}
one sig Player2 extends Player{}
one sig Player3 extends Player{}
one sig Player4 extends Player{}
one sig Player5 extends Player{}
one sig Player6 extends Player{}
one sig Player7 extends Player{}
one sig Player8 extends Player{}

--Rule 5.04(a)
--rule defining the batting order for players
pred battingOrder {
  Player0.next = Player1
  Player1.next = Player2
  Player2.next = Player3
  Player3.next = Player4
  Player4.next = Player5
  Player5.next = Player6
  Player6.next = Player7
  Player7.next = Player8
  Player8.next = Player0
}

--a sig for bases
sig Base {
    next_base: lone Base
}

--Rule 2.03 and 2.02
--there should be exactly 4 bases
one sig FirstBase extends Base{}
one sig SecondBase extends Base{}
one sig ThirdBase extends Base{}
one sig HomePlate extends Base{}

--a sig defining states
sig State {
  outs : one Int,--the number of outs in the inning so far
  runs : one Int,--the number of runs in the inning so far
  at_bat : one Player, --the person at bat in the current state
  on_base : set Base -> Player, --a relation from each base to the player on the base
  people_out: set Player --the set of of people who got out in the state
}


--Rule 506.a.(1)
pred base_order {
   FirstBase.next_base = SecondBase
   SecondBase.next_base = ThirdBase
   ThirdBase.next_base = HomePlate
   HomePlate.next_base = HomePlate
}

--a sig defining Events
sig Event {
    pre: one State,
    post: one State
}

--here are all of the event types that could occur
sig StrikeOut extends Event {  }
sig Hit extends Event {  }
sig FieldOut extends Event {  }
sig Balk extends Event {  }
sig Walk extends Event {  }
sig HBP extends Event {  }
sig Steal extends Event {  }

-- constraints for the first state
state[State] initState {
    at_bat = Player0 -- the first player at bat should be Player0
    outs = sing[0]
    runs = sing[0]
    no on_base
    no people_out
}

--initial state with bases loaded (used for some testing)
state[State] basesLoaded {
    at_bat = Player3
    outs = sing[0]
    runs = sing[0]
    on_base = FirstBase -> Player2 + SecondBase -> Player1 + ThirdBase -> Player0
    no people_out
}

--Rule 5.09(e)
--constraints for the final state
state[State] finalState {
    sum[outs] >= 3 --an inning should end after there are 3 outs
}

--the transition between batting events
transition[State] batterTransition[e: Event] {
   e.pre = this
   e.post = this'
   no people_out & people_out' --the set people_out refreshes in every state
   --people on home plate are removed before the next state
   no (HomePlate.on_base & HomePlate.on_base')
   --for any given base there should be no people out that are also on base
   no (on_base'[Base] & people_out')
   --the new number of people out should only include people who were
   --on base but not on home base in the previous state or were at bat in the
   --previous state
   people_out' in at_bat + on_base[FirstBase + SecondBase + ThirdBase]
   --the new number of people out should include the previous number of outs
   --added to the new number of people out
   outs' = sing[add[sum[outs], #(people_out')]]
   --check that the state is not the last one nad increment the number of runs accordingly
   this' in Event.pre => runs' = sing[add[sum[runs], #(on_base'[HomePlate])]] else {
     sum[runs'] <= add[sum[runs], #(on_base'[HomePlate])]
     sum[runs'] >= sum[runs]
   }

   --Rule 9.15
   --if the event is a strike out, the current batter should get out,
   --the people on base should stay the same, and the new batter should
   --be the current batter's next player
   e in StrikeOut implies {
      at_bat in people_out'
      on_base' = on_base
      at_bat' = at_bat.next
   }

   --Rule 5.05
   --if the event is a hit, the current batter should be in the next on_base relation,
   --everyone in the next on_base relation should only include those
   --who were on first, second, and third bases in the previous state and the batter,
   --anyone who was on the first three bases in the previous state
   --should be either in the new on_base relation or in the new people_out (no teleporting players)
   --the new batter should be the current batter's next
   e in Hit implies {
       at_bat in on_base'[Base]
       on_base'[Base] in on_base[FirstBase + SecondBase + ThirdBase] + at_bat
       on_base[FirstBase + SecondBase + ThirdBase] in on_base'[Base] + people_out'
       at_bat' = at_bat.next
   }

   --if the event is a field out, the current batter should be in the next people_out set,
   --anyone in the new on_base relation should have been in the previous on_base relation,
   --anyone on first, second or third base in the old on_base relation should be in
   --the new on_base relation or in the new set of people_out,
   --the batter in the next state should be the current batter's next
   e in FieldOut implies {
       at_bat in people_out'
       on_base'[Base] in on_base[FirstBase + SecondBase + ThirdBase]
       on_base[FirstBase + SecondBase + ThirdBase] in on_base'[Base] + people_out'
       at_bat' = at_bat.next
   }

   --Rule 5.06.b(3)
   --if the event is a balk, the next batter stays the same as the current batter,
   --there should be some people in on_base, there should be no one on the new first base,
   --and for all bases other than the home plate, the player on the next bases should be
   --in the new on_base relation iff the player is on the current base in the previous state
   e in Balk implies {
       some on_base
       no people_out'
       at_bat' = at_bat
       all b : Base - HomePlate | all p: Player | ((b.next_base -> p) in on_base') iff
       ((b -> p) in on_base)
       no FirstBase.on_base'
   }

   --Rule 9.14
   --if the event is a walk, no one should get out, the batter should rotate
   --if there is no one on first base, then the new on_base relation should include the
   --people on second and third in the previous state as well as the batter on first base
   --if there is no one on second base, the new on_base relation should include the
   --previous on_base relation as well as the batter on first base, the person on third base
   --in the previous state except for the person previously on first base
   --otherwise, any player on the next base of any given base is in the new on_base relation
   --iff that same player is on the current base in the previous on_base relation and
   --the person on first base in the next state should be the current batter
   e in Walk implies {
       no people_out'
       at_bat' = at_bat.next
       (no on_base[FirstBase]) implies on_base' = (SecondBase -> on_base[SecondBase]) +
       (ThirdBase -> on_base[ThirdBase]) + (FirstBase -> at_bat)
       else {
            no on_base[SecondBase] implies on_base' = on_base + (FirstBase -> at_bat) +
            (SecondBase -> on_base[FirstBase]) - (FirstBase -> on_base[FirstBase])
            else {
                all b : Base - HomePlate | all p: Player | ((b.next_base -> p) in on_base') iff
                ((b -> p) in on_base)
                on_base'[FirstBase] = at_bat
            }
       }
   }

   --Rule 9.07
   --if the event is a steal, there should be more than 0 people on base,
   --the people in the new on_base and new people_out should have been in the previous
   --relation on_base of the first three bases
   --people on the first three bases in the previous state should be in the new on_base relation
   --or in the new set of people_out
   --the batter should stay the same
   e in Steal implies {
       some on_base
       (on_base'[Base] + people_out') in on_base[FirstBase + SecondBase + ThirdBase]
       on_base[FirstBase + SecondBase + ThirdBase] in on_base'[Base] + people_out'
       at_bat' = at_bat
   }

   --Rule 5.06.c(1)
   --if the event is a hit-by-pitch, the new batter should be the previous batter's next,
   --if there is no one on first base in the previous state, the next state should
   --include whoever was on second base in the previous state (still on second base),
   --whoever was on third base in the previous state (still on third base), and
   --whoever was at bat in the previous state should be on first base
   --otherwise, if there was no one on second base in the previous state, the new on_base
   --relation should include everything from the previous on_base relation, except
   --with the person previously on first base replaced with the batter in the new state,
   --and the person on second base should be the person who was previously on first base
   --otherwise, any player on any given base's next base should be in the new on_base relation
   --iff that same player is on the current base in the previous state, and the batter
   --should be on first base in the new state
   e in HBP implies {
       at_bat' = at_bat.next
       (no on_base[FirstBase]) implies on_base' = (SecondBase -> on_base[SecondBase]) +
       (ThirdBase -> on_base[ThirdBase]) + (FirstBase -> at_bat)
       else {
            no on_base[SecondBase] implies on_base' = on_base + (FirstBase -> at_bat) +
            (SecondBase -> on_base[FirstBase]) - (FirstBase -> on_base[FirstBase])
            else {
                all b : Base - HomePlate | all p: Player | ((b.next_base -> p) in on_base') iff
                ((b -> p) in on_base)
                on_base'[FirstBase] = at_bat
            }
       }
       no people_out'
   }
}

--Rule 506.a.(1)
pred rightToBase {
    all s : State | {
        all p : Player | lone ((s.on_base).p)
    }
}

--Rule 506.a.(2)
pred loneBaseOwner {
    all s : State | {
        all b : Base - HomePlate | lone (s.on_base)[b]
    }
}

--Rule 509.b.(9)
pred runInOrder {
    all e : Event | {
        e.pre.at_bat in e.post.on_base[Base] => (e.post.on_base).Player in (e.post.on_base).(e.pre.at_bat).*next_base
        
        all p1 : ((FirstBase + SecondBase + ThirdBase).((e.pre).on_base)) - e.post.people_out |
            all p2: ((FirstBase + SecondBase + ThirdBase).((e.pre).on_base)) - e.post.people_out |
                (((e.pre).on_base).p2 in (((e.pre).on_base).p1).*next_base) implies
                (((e.post).on_base).p2 in (((e.post).on_base).p1).*next_base)
    }
}

--a transition between states
transition[State] stateTransition {
    one e: Event | batterTransition[this, this', e]
}

--predicate for testing and debugging
pred wellFormedEvent {
    -- events include all possible event types
    Event = Hit + StrikeOut + Balk + HBP + FieldOut + Walk + Steal
    --#(Walk & Event) > 1
    --#(HBP & Event) > 1
    --#(Steal & Event) > 1
}             

--keep all of the rules in one place
pred allTheRules {
    --How the field is laid out
    battingOrder
    base_order
    wellFormedEvent

    --Baserunning rules
    rightToBase
    loneBaseOwner
    runInOrder
}


trace<|State, initState, stateTransition, finalState|> fullInning {}
--run<|fullInning|> {allTheRules} for exactly 9 Player, exactly 4 Base, 5 State, 4 Event, exactly 1 Hit, exactly 3 FieldOut

trace<|State, _, stateTransition, _|> traces {}


--If you change the 6 states to 5 states it becomes SAT
--run<|traces|> {allTheRules} for exactly 9 Player, exactly 6 State, exactly 5 Event, exactly 4 Base

---------------------------------------------Tests--------------------------------------------------
--setup for tests
inst boiler{
    Player0 = Player00
    Player1 = Player10
    Player2 = Player20
    Player3 = Player30
    Player4 = Player40
    Player5 = Player50
    Player6 = Player60
    Player7 = Player70
    Player8 = Player80
    FirstBase = FirstBase0
    SecondBase = SecondBase0
    ThirdBase = ThirdBase0
    HomePlate = HomePlate0
    Base = FirstBase0 + SecondBase0 + ThirdBase0 + HomePlate0
}

--test a triple
inst testOneTriple {
    boiler
    Event = Hit0
    State = State0 + State1
    Hit = Hit0
    pre = Hit0 -> State0
    post = Hit0 -> State1
    on_base = State1 -> (ThirdBase0 -> Player00)
    at_bat = State0 -> Player00 + State1 -> Player10
    outs = State0 -> sing[0] + State1 -> sing[0]
    runs = State0 -> sing[0] + State1 -> sing[0]   
}

--test a triple with a random run
inst testTripleWithRandomRun {
    boiler
    Event = Hit0
    State = State0 + State1
    Hit = Hit0
    pre = Hit0 -> State0
    post = Hit0 -> State1
    on_base = State1 -> (ThirdBase0 -> Player00)
    at_bat = State0 -> Player00 + State1 -> Player10
    outs = State0 -> sing[0] + State1 -> sing[0]
    runs = State0 -> sing[0] + State1 -> sing[5]
}

--test that a runner who starts after can't pass a runner who was before
inst batterCantPass {
    boiler
    Event = Hit0 + Hit1
    State = State0 + State1 + State2
    Hit = Hit0 + Hit1
    pre = Hit0 -> State0 + Hit1 -> State1
    post = Hit0 -> State1 + Hit1 -> State2
    on_base = State1 -> (ThirdBase0 -> Player00) + State2 -> (ThirdBase0 -> Player00) + State2 -> (HomePlate0 -> Player10)   
    at_bat = State0 -> Player00 + State1 -> Player10 + State2 -> Player20
    outs = State0 -> sing[0] + State1 -> sing[0] + State2 -> sing[0]
    runs = State0 -> sing[0] + State1 -> sing[0] + State2 -> sing[1]
}

--test that home runs are counted correctly
inst homerun {
    boiler
    Event = Hit0 + Hit1
    State = State0 + State1 + State2
    Hit = Hit0 + Hit1
    pre = Hit0 -> State0 + Hit1 -> State1
    post = Hit0 -> State1 + Hit1 -> State2
    on_base = State1 -> (ThirdBase0 -> Player00) + State2 -> (HomePlate0 -> Player00) + State2 -> (HomePlate0 -> Player10)
    at_bat = State0 -> Player00 + State1 -> Player10 + State2 -> Player20
    outs = State0 -> sing[0] + State1 -> sing[0] + State2 -> sing[0]
    runs = State0 -> sing[0] + State1 -> sing[0] + State2 -> sing[2]
}

--test that one base can't have more than one player at a time
inst testSingleBaseOwner {
    boiler
    Event = Hit0 + Hit1
    State = State0 + State1 + State2
    Hit = Hit0 + Hit1
    pre = Hit0 -> State0 + Hit1 -> State1
    post = Hit0 -> State1 + Hit1 -> State2
    on_base = State1 -> (ThirdBase0 -> Player00) + State2 -> (ThirdBase0 -> Player00) + State2 -> (ThirdBase0 -> Player10)   
    at_bat = State0 -> Player00 + State1 -> Player10 + State2 -> Player20
    outs = State0 -> sing[0] + State1 -> sing[0] + State2 -> sing[0]
    runs = State0 -> sing[0] + State1 -> sing[0] + State2 -> sing[0]
}

--test that a player can't be on more than one base at a time
inst testRightToBase {
    boiler
    Event = Hit0
    State = State0 + State1
    Hit = Hit0
    pre = Hit0 -> State0
    post = Hit0 -> State1
    on_base = State1 -> (ThirdBase0 -> Player00) + State1 -> (FirstBase0 -> Player00)
    at_bat = State0 -> Player00 + State1 -> Player10
    outs = State0 -> sing[0] + State1 -> sing[0]
    runs = State0 -> sing[0] + State1 -> sing[0] 
}

--test a series of strikeouts and steal
inst testStrikeoutSteal {
    boiler
    Event = StrikeOut0 + Steal0
    State = State0 + State1 + State2
    StrikeOut = StrikeOut0
    Steal = Steal0
    pre = Steal0 -> State0 + StrikeOut0 -> State1
    post = Steal0 -> State1 + StrikeOut0 -> State2
    on_base = State0 -> (FirstBase0 -> Player10) + State0 -> (ThirdBase0 -> Player00) +
                State1 -> (SecondBase0 -> Player10) + State1 -> (HomePlate0 -> Player00) +
                 State2 -> (SecondBase0 -> Player10)   
    at_bat = State0 -> Player20 + State1 -> Player20 + State2 -> Player30
    outs = State0 -> sing[1] + State1 -> sing[1] + State2 -> sing[2]
    runs = State0 -> sing[0] + State1 -> sing[1] + State2 -> sing[1]
}

--test that our model isn't able to check whether runs occurred before or after 3 outs were achieved
inst differentNumberRuns {
    boiler
    Event = FieldOut0
    State = State0 + State1
    FieldOut = FieldOut0
    pre = FieldOut0 -> State0
    post = FieldOut0 -> State1
    runs = State0 -> sing[0] + State1 -> sing[1]
    on_base = State0 -> (SecondBase0 -> Player10) + State0 -> (ThirdBase0 -> Player00) + State0 -> (FirstBase0 -> Player20) +
                 State1 -> (HomePlate0 -> Player00) + State1 -> (HomePlate0 -> Player10) + State1 -> (HomePlate0 -> Player20)
    at_bat = State0 -> Player30 + State1 -> Player40
    outs = State0 -> sing[2] + State1 -> sing[3]

}

--test that our model isn't able to check whether runs occurred before or after 3 outs were achieved
inst differentNumberRuns1 {
    boiler
    Event = FieldOut0
    State = State0 + State1
    FieldOut = FieldOut0
    pre = FieldOut0 -> State0
    post = FieldOut0 -> State1
    runs = State0 -> sing[0] + State1 -> sing[2]
    on_base = State0 -> (SecondBase0 -> Player10) + State0 -> (ThirdBase0 -> Player00) + State0 -> (FirstBase0 -> Player20) +
                 State1 -> (HomePlate0 -> Player00) + State1 -> (HomePlate0 -> Player10) + State1 -> (HomePlate0 -> Player20)
    at_bat = State0 -> Player30 + State1 -> Player40
    outs = State0 -> sing[2] + State1 -> sing[3]

}

--test that our model isn't able to check whether runs occurred before or after 3 outs were achieved
inst differentNumberRuns2 {
    boiler
    Event = FieldOut0
    State = State0 + State1
    FieldOut = FieldOut0
    pre = FieldOut0 -> State0
    post = FieldOut0 -> State1
    runs = State0 -> sing[0] + State1 -> sing[3]
    on_base = State0 -> (SecondBase0 -> Player10) + State0 -> (ThirdBase0 -> Player00) + State0 -> (FirstBase0 -> Player20) +
                 State1 -> (HomePlate0 -> Player00) + State1 -> (HomePlate0 -> Player10) + State1 -> (HomePlate0 -> Player20)
    at_bat = State0 -> Player30 + State1 -> Player40
    outs = State0 -> sing[2] + State1 -> sing[3]
}

--test that it is possible for runners to move backwards given the rules of baseball
inst backwardRunners {
    boiler
    Event = Steal0
    State = State0 + State1
    Steal = Steal0
    pre = Steal0 -> State0
    post = Steal0 -> State1
    on_base = State0 -> (SecondBase0 -> Player00) + State0 -> (FirstBase0 -> Player10) + State1 -> (FirstBase0 -> Player00)
    outs = State0 -> sing[0] + State1 -> sing[1]
}

--instance to test a walk
inst testWalk {
    boiler
    Event = Walk0
    State = State0 + State1
    Walk = Walk0
    pre = Walk0 -> State0
    post = Walk0 -> State1
    on_base = State0 -> (FirstBase0 -> Player20) + State0 -> (SecondBase0 -> Player10) + State0 -> (ThirdBase0 -> Player00) +
                State1 -> (SecondBase0 -> Player20) + State1 -> (FirstBase0 -> Player30) + State1 -> (ThirdBase0 -> Player10) + State1 -> (HomePlate0 -> Player00)
    at_bat = State0 -> Player30 + State1 -> Player40
    outs = State0 -> sing[1] + State1 -> sing[1]
    runs = State0 -> sing[3] + State1 -> sing[4]
} 

--ensure that the number of outs can only ever stay the same or increase
pred outsGoDown {
    some e : Event | 
        sum[(e.pre.outs)] > sum[(e.post.outs)]
}

--ensure that runs will increase or stay the same
pred runsGoDown {
    some e : Event | 
        sum[(e.pre.runs)] > sum[(e.post.runs)]
}

--every player who is at some point on base was at bat at some point before
pred battedToGetOn {
    all e : Event |
        all p: Player |
            (p in Base.(e.post.on_base)) implies (p in e.^pre.at_bat)
}

--run<|traces|> {allTheRules} for differentNumberRuns 

--run tests
test expect {
    --test a single triple
    justATriple: <|traces|> {allTheRules} for testOneTriple is sat
    --test a triple with a random run
    cheekyTriple: <|traces|> {allTheRules} for testTripleWithRandomRun is unsat
    --test that players can't pass one another
    noPassing: <|traces|> {allTheRules} for batterCantPass is unsat
    --test that home runs are counted correctly
    hitEmHome: <|traces|> {allTheRules} for homerun is sat
    --check that player's cant share bases
    noSharing: <|traces|> {allTheRules} for testSingleBaseOwner is unsat
    --check that a player can't be on more than one base at a same time
    noQuantumPlayers: <|traces|> {allTheRules} for testRightToBase is unsat
    --check a situation with a strikeout and steal
    strikeoutsAndSteal: <|traces|> {allTheRules} for testStrikeoutSteal is unsat
    --check a complicated sequence of events
    lotsOfDifferentEvents: <|traces|> {allTheRules} for exactly 9 State, exactly 8 Event, exactly 3 Hit, exactly 1 HBP,
                                                                          exactly 1 Walk, exactly 1 Balk, exactly 1 FieldOut,
                                                                          exactly 1 Steal, exactly 1 StrikeOut, exactly 9 Player, exactly 4 Base is sat
    --demonstrate that it is possible to get a different number of runs with the same sequence of events
    manyRuns: <|traces|> {allTheRules} for differentNumberRuns is sat
    manyRuns1: <|traces|> {allTheRules} for differentNumberRuns1 is sat
    manyRuns2: <|traces|> {allTheRules} for differentNumberRuns2 is sat
    --demonstrate that it is possible for runners to go backwards (Segura's move was possible given the rules we modelled)
    --See https://youtu.be/HZM1JcJwo9E for the video
    backwardsBoi:  <|traces|> {allTheRules} for backwardRunners is sat
    --test a walk
    loadedWalk: <|traces|> {allTheRules} for testWalk is sat
    --test that runs only increase or stay the same - takes an extremely long time
    runsIncrease: <|fullInning|> {allTheRules and runsGoDown} for exactly 6 State, exactly 5 Event is unsat
    --test that checks that outs only increase or stay the same -- takes an extremely long time
    outsIncrease: <|fullInning|> {allTheRules and outsGoDown} for exactly 3 State, exactly 2 Event is unsat
    --ensure that no players can end up on base without batting first
    noSneakingOnBase:  <|fullInning|> {allTheRules and battedToGetOn} for exactly 6 State, exactly 5 Event is sat 
} 






