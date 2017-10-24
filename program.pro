domains 

action=to_table(block,block,table);to_block(block,table,block);
block_to_block(block,block,block);table_to_table(block,table,table) 
/* action ‘action’ is composite object that sets moving of one block
from another block to the table, from the table to the block, from the
block to the block or from the table to the table */ 

on=on1(block,block);on2(block,table) 
/* ‘on’ is composite object that states the fact block is on another block
or on the table */

on1=on1(block,block) 
on2=on2(block,table) 

block=a;b;c;d;f;g;h /* we have only 7 blocks */
table=k;l;m;n;o;p;q /* also we have only 7 tables */
a,b,c,d,f,g,h,k,l,m,n,o,p,q=symbol

state=on* 
/* state is a list of objects ‘on’ that describes placing of all the blocks
on the tables. */ 

visited=state* 
plan=action* 

predicates 

nondeterm transform_re(state,state,visited,integer,plan,visited) 
/* (i, i, i, i, o, o) – builds plan of actions for transition from start
state to end state. */ 

nondeterm legal_action(action,state) 
/* (i, i) – checks applicability of action ‘action’ in the state ‘state’ */ 

nondeterm update(action,state,state) 
/* (i, i, o) – computes new state after applying an action */ 

nondeterm substitute(on,on,state,state) 
/* (i, i, i, o) – recursive part of ‘update’ */ 

nondeterm block(block) 
nondeterm table(table) 
nondeterm member(on,state) 
nondeterm statemember(state,visited) 
nondeterm append(visited,visited,visited) 

print_plan(plan,visited) 
/* auxiliary predicate for printing the plans */ 

print_plan_re(plan,visited) 
/* recursive part of predicate ‘print_plan’ */ 

nondeterm test_plan(state,state,plan) 
/* Verification of the found plan for correctness */ 

initial_state(state) 
final_state(state) 

nondeterm block_is_ontop(block, state) 
/* (i, i) – checks if block is on the top, i.e. nothing lies on it */ 

nondeterm table_is_free(table, state) 
/* (i, i) – checks if nothing lies on the table */ 

nondeterm transform(state,state,plan,visited) 

nondeterm good_action(action) 
/* (i) – checks if action ‘action’ is ‘good’ (i.e. enough useful)*/ 

clauses 

/* Predicate ‘transform’ that launches recursive predicate ‘transform_re’ */ 
transform(State1, State2, Plan, Visited) :- 
transform_re(State1, State2, [State1], 0, Plan, Visited), 
write("\n\nSolution:\nI = ",State1,"\nF = ",State2), nl, 
write("Action\t\tNew State"), nl, 
print_plan(Plan, Visited), nl. 
/* Searching for plan of actions from transition from given start state to
the end state */ 

transform_re(State2, State2, VisitedOut, _, [], VisitedOut). 
/* Condition of recursion ending is transition to the end state */ 

/* Performs if action is ‘good’*/ 
transform_re(State1, State2, Visited, WrongNum,[Action|Actions], VisitedOut):- 
/* transforms state ‘State1’ to the state ‘State2’ as a result of execuiton 
* of action ‘Action’ that is located in the head of the list [Action|Actions],
* if action ‘Action’ is applicable in the state ‘State1’ and do not belong
* to the list ‘Visited’ */ 
legal_action(Action, State1), 
/* Check of applicability of action ‘Action’ in the state ‘State1’ */ 
good_action(Action), 
/* Check if action ‘Action’ is ‘good’ in the state ‘State1’ */ 
update(Action, State1, State), 
/* Execution of action ‘Action’ in the state ‘State1’ gives
* transition to the state ‘State’ in result */ 
not(statemember(State,Visited)), 
/* Check if  state ‘State’ do not belong* to the list ‘Visited’ */ 
append(Visited, [State], Visited1), 
transform_re(State,State2,Visited1,WrongNum,Actions,VisitedOut),!. 
/* Transforms state ‘State’ to the state ‘State2’ as a result of
* execution of actions that are located in the head of list ‘Action’,
* if it’s applicable in the state ‘State’ */ 

/* Executes if action is ‘bad’ */ 
transform_re(State1, State2, Visited, WrongNum,[Action|Actions], VisitedOut):- 
WrongNum < 10, 
/* Counter of ‘bad’ actions */ 

legal_action(Action, State1), 
not(good_action(Action)), 
/* Checks if action ‘Action’ is ‘bad’ in the state ‘State1’ */ 
update(Action, State1, State), 
not(statemember(State,Visited)), 
WrongNum1 = WrongNum + 1, 
append(Visited, [State], Visited1), 
transform_re(State,State2,Visited1,WrongNum1,Actions,VisitedOut),!. 

/* Checks if given action is applicable in given state */ 
legal_action(to_table(Block1,Block2,Table),State):- 
/* Checks if action of moving of block ‘Block1’ from block ‘Block2’
* to table ‘Table’ is applicable in the state ‘State’ */ 

block(Block1), 
block(Block2), 
not(Block1=Block2), 
member(on1(Block1, Block2), State), 
/* Checks if block ‘Block1’ is on the block ‘Block2’ in the state ‘State’ */ 
block_is_ontop(Block1, State), 
/* Checks if block ‘Block1’ is on the top and is accessible to move */ 
table(Table), 
table_is_free(Table, State). 
/*Checks if there is no block on the table ‘Table’ */ 

legal_action(to_block(Block1,Table,Block2),State):- 
/* Checks if given action is applicable in given state */ 
legal_action(to_table(Block1,Block2,Table),State):- 
/* Checks if action of moving of block ‘Block1’ from block ‘Block2’
* to table ‘Table’ is applicable in the state ‘State’ */  
block(Block1), 
table(Table), 
member(on2(Block1,Table),State), 
/* Checks if block ‘Block1’ is on the table ‘Table’ in the state ‘State’ */ 
block(Block2), 
not(Block1=Block2), 
/* Checks if block ‘Block1’ isn’t equal to block ‘Block2’ */ 
block_is_ontop(Block1, State), 
/* Checks if block ‘Block1’ is on the top and is accessible to move */ 
block_is_ontop(Block2, State). 
/* Checks if block ‘Block2’ is on the top and we can put another block on it */ 

legal_action(block_to_block(Block1,Block2,Block3),State):- 
block(Block1), 
block(Block3), 
not(Block1=Block3), 
member(on1(Block1,Block2),State), 
block_is_ontop(Block1, State), 
block(Block2), 
not(Block1=Block2), 
block_is_ontop(Block2, State). 

legal_action(table_to_table(Block1,Table1,Table2),State):- 
block(Block1), 
table(Table1),
table(Table2),
table_is_free(Table2,State),
not(Table1=Table2), 
member(on2(Block1,Table1),State), 
block_is_ontop(Block1, State). 

/* Defines if situations are enough good for moving from table to block
* or from block to table or from table to table ot from block to block */ 
good_action(to_table(Block1,_,Table)):- 
final_state(FinalState), 
member(on2(Block1,Table), FinalState). 

good_action(to_block(Block1,_,Block2)):- 
final_state(FinalState), 
member(on1(Block1,Block2), FinalState). 

good_action(block_to_block(Block1,_,Block3)):- 
final_state(FinalState), 
member(on1(Block1,Block3), FinalState). 

good_action(table_to_table(Block1,_,Table2)):- 
final_state(FinalState), 
member(on2(Block1,Table2), FinalState). 

/* Checks if element is in the list ‘on’ */ 
member(ON, [ON | _]). 
member(ON, [_ | Tail]) :- member(ON, Tail). 

/* Checks if element is in the list ‘(on*)’ */ 
statemember(State,[State|_]). 
statemember(State,[_|Tail]) :- statemember(State,Tail). 

/* Writes one list to the end of another list */ 
append([],Visited,Visited). 
append([H|L1],List2,[H|L3]) :- append(L1,List2,L3). 

/* Auxiliary predicate for readable printing plans on the screen */ 
print_plan(Plan, [VH|VT]) :- write("- - - Initial - - -\t", VH), nl, print_plan_re(Plan,VT). 
print_plan_re([], []). 
print_plan_re([PH|PT], [VH|VT]) :- write(PH, "\t", VH), nl, print_plan_re(PT, VT). 

/* Computes new state after applying given action */ 
update(to_block(Block1,Table,Block2),State,State1):- 
substitute(on2(Block1,Table),on1(Block1,Block2),State,State1). 

update(block_to_block(Block1,Block2,Block3),State,State1):- 
substitute(on1(Block1,Block2),on1(Block1,Block3),State,State1). 

update(to_table(Block1,Block2,Table),State,State1):- 
substitute(on1(Block1,Block2),on2(Block1,Table),State,State1). 

update(table_to_table(Block1,Table1,Table2),State,State1):- 
substitute(on2(Block1,Table1),on2(Block1,Table2),State,State1). 

/* substitute(X, X1, State, State1) (i, i, i, o) replaces element X in
the list ‘State’ for element X1 and returns new list ‘State1’ */ 
substitute(X, X1, [X | Tail], [X1 | Tail]). 
substitute(X, X1, [H | Tail], [H | NewTail]) :- 
substitute(X, X1,
Tail, NewTail). 

/* Declares start and end states */ 
initial_state([on2(a,q),on1(b,h),on1(c,d),on1(d,a),on2(f,p),on1(g,f),on1(h,g)]).
final_state([on2(a,n),on1(b,h),on1(c,d),on1(d,a),on1(f,c),on1(g,f),on1(h,g)]).
        /* We have only 7 blocks */
    block(a).
    block(b).
    block(c).
    block(d).
    block(f).
    block(g).
    block(h).

        /* We also have only 7 tables */
    table(k).
    table(l).
    table(m).
    table(n).
    table(o).
    table(p).
    table(q).
/* --------------- New predicates -------------------- */ 
/* Checks if block ‘Block1’ is on the top. It works only on (i, i) but don’t
work on (o, i) */ 
block_is_ontop(Block1, State) :- 
member(on1(_, Block1), State), !, 1=2. 
/* If there is any block that lies on given block, then it’s irrevocable failure
of search */ 

block_is_ontop(Block1, State) :- 
member(on2(Block1, _), State), !. 
/* Else checks if block is in current configuration, */ 

block_is_ontop(Block1, State) :- member(on1(Block1, _), State). 
/* i.e. it lies on the table or on another block */ 

/* Checks if there is nothing on the table ‘Table1’ 
* It works only on (i, i), but don’t work on (o, i) */ 
table_is_free(Table1, State) :- 
member(on2(_, Table1), State), !, 1=2. 
/* If there is any block that lies on the table, then it’s irrevocable failure
of search */ 

table_is_free(Table1, _) :- table(Table1). 
/* Else checks if the table is presented in current configuration */ 

/* Predicate for checking of found plan for correctness */ 
test_plan(F,F,[]) :- write("Plan succeded\n"). 
test_plan(S1,F,[Action|Tail]):-legal_action(Action,S1), update(Action,S1,S2), test_plan(S2,F,Tail). 

goal 

initial_state(I),final_state(F),transform(I,F,Plan,Visited), 
test_plan(I,F,Plan).