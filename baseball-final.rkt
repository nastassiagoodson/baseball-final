#lang forge
--a sig defining players
sig Player {
  next : one Player
}

--there should be 9 players
one sig Player0 extends Player{}
one sig Player1 extends Player{}
one sig Player2 extends Player{}
one sig Player3 extends Player{}
one sig Player4 extends Player{}
one sig Player5 extends Player{}
one sig Player6 extends Player{}
one sig Player7 extends Player{}
one sig Player8 extends Player{}

--rule defining the batting order for players
pred batting_order {
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
    nextBase: lone Base
}

--there should be exactly 4 bases
one sig FirstBase extends Base{}
one sig SecondBase extends Base{}
one sig ThirdBase extends Base{}
one sig HomePlate extends Base{}

--a sig defining states
sig State {
  outs : one Int,--the number of outs in the inning so far
  runs : one Int,--the number of runs in the inning so far
  atBat : one Player, --the person at bat in the current state
  on_base : set Base -> Player, --a relation from each base to the player on the base
  people_out: set Player --the set of of people who got out in the state
  --outsAndRunsOrder: Player -> Player
}


--Rule 506.a.(1)
pred base_order {
   FirstBase.nextBase = SecondBase
   SecondBase.nextBase = ThirdBase
   ThirdBase.nextBase = HomePlate
   HomePlate.nextBase = HomePlate
}

--a sig defining Events
sig Event {
    pre: one State,
    post: one State
}

--here are all of the event types that could occur
sig StrikeOut extends Event {  }
sig Hit extends Event {  }
sig Fieldout extends Event {  }
sig Balk extends Event {  }
sig Walk extends Event {  }
sig HBP extends Event {  }
sig Steal extends Event {  }

-- constraints for the first state
state[State] initState {
    atBat = Player0 -- the first player at bat should be Player0
    outs = sing[0]
    runs = sing[0]
    no on_base
    no people_out
}

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
   people_out' in atBat + on_base[FirstBase + SecondBase + ThirdBase]
   --the new number of people out should include the previous number of outs
   --added to the new number of people out
   outs' = sing[add[sum[outs], #(people_out')]]
   --keeping this???
   e.post in State.pre => runs' = sing[add[sum[runs], #(on_base'[HomePlate])]] else {
      runs' <= sing[add[sum[runs], #(on_base'[HomePlate])]]
      runs' >= runs
   }
   --if the event is a strike out, the current batter should get out,
   --the people on base should stay the same, and the new batter should
   --be the current batter's next player
   e in StrikeOut implies {
      atBat in people_out'
      on_base' = on_base
      atBat' = atBat.next
   }
   
   --if the event is a hit, the current batter should be in the next on_base relation,
   --everyone in the next on_base relation should only include those
   --who were on first, second, and third bases in the previous state and the batter,
   --anyone who was on the first three bases in the previous state
   --should be either in the new on_base relation or in the new people_out (no teleporting players)
   --the new batter should be the current batter's next
   e in Hit implies {
       atBat in on_base'[Base]
       on_base'[Base] in on_base[FirstBase + SecondBase + ThirdBase] + atBat
       on_base[FirstBase + SecondBase + ThirdBase] in on_base'[Base] + people_out'
       atBat' = atBat.next
   }

   --if the event is a field out, the current batter should be in the next people_out set,
   --anyone in the new on_base relation should have been in the previous on_base relation,
   --anyone on first, second or third base in the old on_base relation should be in
   --the new on_base relation or in the new set of people_out,
   --the batter in the next state should be the current batter's next
   e in Fieldout implies {
       atBat in people_out'
       on_base'[Base] in on_base[Base]
       on_base[FirstBase + SecondBase + ThirdBase] in on_base'[Base] + people_out'
       atBat' = atBat.next
   }

   --if the event is a balk, the next batter stays the same as the current batter,
   --there should be some people in on_base, there should be no one on the new first base,
   --and for all bases other than the home plate, the player on the next bases should be
   --in the new on_base relation iff the player is on the current base in the previous state
   e in Balk implies {
       some on_base
       no people_out'
       atBat' = atBat
       all b : Base - HomePlate | all p: Player | ((b.nextBase -> p) in on_base') iff
       ((b -> p) in on_base)
       no FirstBase.on_base'
   }

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
       atBat' = atBat.next
       (no on_base[FirstBase]) implies on_base' = (SecondBase -> on_base[SecondBase]) +
       (ThirdBase -> on_base[ThirdBase]) + (FirstBase -> atBat)
       else {
            no on_base[SecondBase] implies on_base' = on_base + (FirstBase -> atBat) +
            (SecondBase -> on_base[FirstBase]) - (FirstBase -> on_base[FirstBase])
            else {
                all b : Base - HomePlate | all p: Player | ((b.nextBase -> p) in on_base') iff
                ((b -> p) in on_base)
                on_base'[FirstBase] = atBat
            }
       }
   }
   
   e in Steal implies {
       some on_base
       (on_base'[Base] + people_out') in on_base[FirstBase + SecondBase + ThirdBase]
       on_base[FirstBase + SecondBase + ThirdBase] in on_base'[Base] + people_out'
       atBat' = atBat
   }
   
   e in HBP implies {
       atBat' = atBat.next
       (no on_base[FirstBase]) implies on_base' = (SecondBase -> on_base[SecondBase]) +
       (ThirdBase -> on_base[ThirdBase]) + (FirstBase -> atBat)
       else {
            no on_base[SecondBase] implies on_base' = on_base + (FirstBase -> atBat) +
            (SecondBase -> on_base[FirstBase]) - (FirstBase -> on_base[FirstBase])
            else {
                all b : Base - HomePlate | all p: Player | ((b.nextBase -> p) in on_base') iff
                ((b -> p) in on_base)
                on_base'[FirstBase] = atBat
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
        (e.post.on_base).Player in (e.post.on_base).(e.pre.atBat).*nextBase
        
        all p1 : ((FirstBase + SecondBase + ThirdBase).((e.pre).on_base)) - e.post.people_out |
            all p2: ((FirstBase + SecondBase + ThirdBase).((e.pre).on_base)) - e.post.people_out |
                (((e.pre).on_base).p2 in (((e.pre).on_base).p1).*nextBase) implies
                (((e.post).on_base).p2 in (((e.post).on_base).p1).*nextBase)
    }
}

--a transition between states
transition[State] stateTransition {
    one e: Event | batterTransition[this, this', e]
}

--predicate for testing and debugging
pred wellFormedEvent {
    -- events include all possible event types
    Event = Hit + StrikeOut + Balk + HBP + Fieldout + Walk + Steal
    --#(Walk & Event) > 1
    --#(HBP & Event) > 1
    --#(Steal & Event) > 1
}             

--keep all of the rules in one place
pred allTheRules {
    --How the field is laid out
    batting_order
    base_order
    wellFormedEvent

    --Baserunning rules
    rightToBase
    loneBaseOwner
    runInOrder
}


trace<|State, initState, stateTransition, finalState|> fullInning {}
run<|fullInning|> {allTheRules} for exactly 9 Player, exactly 4 Base, 10 State, 9 Event, 4 Hit,
3 HBP, 3 Walk, 3 Balk, 3 Fieldout, 3 Steal, 3 StrikeOut

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
    atBat = State0 -> Player00 + State1 -> Player10
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
    atBat = State0 -> Player00 + State1 -> Player10
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
    atBat = State0 -> Player00 + State1 -> Player10 + State2 -> Player20
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
    atBat = State0 -> Player00 + State1 -> Player10 + State2 -> Player20
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
    atBat = State0 -> Player00 + State1 -> Player10 + State2 -> Player20
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
    atBat = State0 -> Player00 + State1 -> Player10
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
    atBat = State0 -> Player20 + State1 -> Player20 + State2 -> Player30
    outs = State0 -> sing[1] + State1 -> sing[1] + State2 -> sing[2]
    runs = State0 -> sing[0] + State1 -> sing[1] + State2 -> sing[1]
}


--run<|traces|> {allTheRules} for batterCantPass 

--run tests
test expect {
    justATriple: <|traces|> {allTheRules} for testOneTriple is sat
    cheekyTriple: <|traces|> {allTheRules} for testTripleWithRandomRun is unsat
    noPassing: <|traces|> {allTheRules} for batterCantPass is unsat
    hitEmHome: <|traces|> {allTheRules} for homerun is sat
    noSharing: <|traces|> {allTheRules} for testSingleBaseOwner is unsat
    noQuantumPlayers: <|traces|> {allTheRules} for testRightToBase is unsat
    strikeoutsAndSteal: <|traces|> {allTheRules} for testStrikeoutSteal is unsat
    lotsOfDifferentEvents: <|traces|> {allTheRules} for exactly 9 State, exactly 8 Event, exactly 3 Hit, exactly 1 HBP,
                                                                          exactly 1 Walk, exactly 1 Balk, exactly 1 Fieldout,
                                                                           exactly 1 Steal, exactly 1 StrikeOut, exactly 9 Player, exactly 4 Base is sat
} 






