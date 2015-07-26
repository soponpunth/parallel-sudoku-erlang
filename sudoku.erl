-module(sudoku).
%-include_lib("eqc/include/eqc.hrl").
-compile(export_all).

%% %% generators

%% matrix(M,N) ->
%%     vector(M,vector(N,nat())).

%% matrix transpose

transpose([Row]) ->
    [[X] || X <- Row];
transpose([Row|M]) ->
    [[X|Xs] || {X,Xs} <- lists:zip(Row,transpose(M))].

%% prop_transpose() ->
%%     ?FORALL({M,N},{nat(),nat()},
%% 	    ?FORALL(Mat,matrix(M+1,N+1),
%% 		    transpose(transpose(Mat)) == Mat)).

%% map a matrix to a list of 3x3 blocks, each represented by the list
%% of elements in row order

triples([A,B,C|D]) ->
    [[A,B,C]|triples(D)];
triples([]) ->
    [].

blocks(M) ->
    Blocks = [triples(X) || X <- transpose([triples(Row) || Row <- M])],
    lists:append(
      lists:map(fun(X)->
			lists:map(fun lists:append/1, X)
		end,
		Blocks)).

unblocks(M) ->
    lists:map(
      fun lists:append/1,
      transpose(
	lists:map(
	  fun lists:append/1,
	  lists:map(
	    fun(X)->lists:map(fun triples/1,X) end,
	    triples(M))))).

%% prop_blocks() ->
%%     ?FORALL(M,matrix(9,9),
%% 	    unblocks(blocks(M)) == M).

%% decide whether a position is safe

entries(Row) ->
    [X || X <- Row,
	  1 =< X andalso X =< 9].

safe_entries(Row) ->
    Entries = entries(Row),
    lists:sort(Entries) == lists:usort(Entries).

safe_rows(M) ->
    lists:all(fun safe_entries/1,M).

safe(M) ->
    safe_rows(M) andalso
	safe_rows(transpose(M)) andalso
	safe_rows(blocks(M)).

%% fill blank entries with a list of all possible values 1..9

fill(M) ->
    Nine = lists:seq(1,9),
    [[if 1=<X, X=<9 ->
	      X;
	 true ->
	      Nine
      end
      || X <- Row]
     || Row <- M].

%% refine entries which are lists by removing numbers they are known
%% not to be

refine(M) ->
    NewM =
	refine_rows(
	  transpose(
	    refine_rows(
	      transpose(
		unblocks(
		  refine_rows(
		    blocks(M))))))),
    if M==NewM ->
	    M;
       true ->
	    refine(NewM)
    end.

refine_rows(M) ->
    lists:map(fun refine_row/1,M).

refine_row(Row) ->
    Entries = entries(Row),
    NewRow =
	[if is_list(X) ->
		 case X--Entries of
		     [] ->
			 exit(no_solution);
		     [Y] ->
			 Y;
		     NewX ->
			 NewX
		 end;
	    true ->
		 X
	 end
	 || X <- Row],
    NewEntries = entries(NewRow),
    %% check we didn't create a duplicate entry
    case length(lists:usort(NewEntries)) == length(NewEntries) of
	true ->
	    NewRow;
	false ->
	    exit(no_solution)
    end.


refine_all(M) ->
	NewBlock = unblocks(refine_rows(blocks(M))),
	NewCol = transpose(refine_rows(transpose(M))),
	NewRow = refine_rows(M),
    NewM = combine_refine(NewRow,NewCol,NewBlock),
	
    if M==NewM ->
	    M;
       true ->
	    refine_all(NewM)
    end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% parallel version
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% First approach : refining rows of matrix in parallel.

refine_par(M) ->
    NewM =
	refine_rows_par(5,transpose(refine_rows_par(5,transpose(unblocks(refine_rows_par(5,blocks(M))))))),
    if M==NewM ->
	    M;
       true ->
	    refine_par(NewM)
    end.


refine_rows_par(_,[]) -> [];
refine_rows_par(0,M) -> refine_rows(M);
refine_rows_par(D,[R|Rs]) ->
  Parent = self(),
  Ref = make_ref(),
  spawn_link(fun() ->
            	Parent ! {Ref, catch refine_row(R)}
        	end),
  NewRs = refine_rows_par(D-1,Rs),
  receive
    {Ref, {'EXIT', Msg}} -> exit(Msg);
    {Ref, NewR}      -> [NewR | NewRs]
  end.




%% Second approach : refining row,col,block of matrix in parallel.

refine_all_par(0,M) -> refine_all(M);
refine_all_par(D,M) ->
  Parent = self(),
  RefB = make_ref(),
  RefC = make_ref(),
  RefR = make_ref(),
  spawn_link(fun() ->
                 Parent ! {RefB, catch unblocks(refine_rows(blocks(M)))}
             end),
  spawn_link(fun() ->
                 Parent ! {RefC, catch transpose(refine_rows(transpose(M)))}
             end),
  spawn_link(fun() ->
                 Parent ! {RefR, catch refine_rows(M)}
             end),
  NewBlock = receive 
  				{RefB, {'EXIT', Msg1}} -> exit(Msg1);
               	{RefB, B} -> B 
           	 end,
  NewCol = receive 
  				{RefC, {'EXIT', Msg2}} -> exit(Msg2);
                {RefC, C} -> C 
           end,
  NewRow = receive 
  				{RefR, {'EXIT', Msg3}} -> exit(Msg3);
               {RefR, R} -> R 
           end,
  NewM = combine_refine(NewRow,NewCol,NewBlock),
  if M==NewM ->
       M;
     true ->
       refine_all_par(D-1,NewM)
  end.



%% combine refined_row, refined_block, refined_col together using intersection.
combine_refine([],[],[]) -> [];
combine_refine([RR|RRs],[CC|CCs],[BB|BBs]) ->
	[run_intersect(RR,CC,BB) | combine_refine(RRs,CCs,BBs)].
	


run_intersect([],[],[]) -> [];
run_intersect([R|Rs],[C|Cs],[B|Bs]) ->
	if erlang:is_list(R) and erlang:is_list(C) and erlang:is_list(B) ->
		Result = intersect(R,C,B),
		[Result | run_intersect(Rs,Cs,Bs)];
	   true -> 
	   	[R | run_intersect(Rs,Cs,Bs)]
	end.   	


intersect(L1,L2,L3) ->
	A = sets:from_list(L1),
	B = sets:from_list(L2),
	AB = sets:intersection(A,B),
	C = sets:from_list(L3),
	sets:to_list(sets:intersection(C,AB)).




is_exit({'EXIT',_}) ->
    true;
is_exit(_) ->
    false.

%% is a puzzle solved?

solved(M) ->
    lists:all(fun solved_row/1,M).

solved_row(Row) ->
    lists:all(fun(X)-> 1=<X andalso X=<9 end, Row).

%% how hard is the puzzle?

hard(M) ->		      
    lists:sum(
      [lists:sum(
	 [if is_list(X) ->
		  length(X);
	     true ->
		  0
	  end
	  || X <- Row])
       || Row <- M]).

%% choose a position {I,J,Guesses} to guess an element, with the
%% fewest possible choices

guess(M) ->
    Nine = lists:seq(1,9),
    {_,I,J,X} =
	lists:min([{length(X),I,J,X}
		   || {I,Row} <- lists:zip(Nine,M),
		      {J,X} <- lists:zip(Nine,Row),
		      is_list(X)]),
    {I,J,X}.

%% given a matrix, guess an element to form a list of possible
%% extended matrices, easiest problem first.

guesses(M) ->
    {I,J,Guesses} = guess(M),
    Ms = [catch refine(update_element(M,I,J,G)) || G <- Guesses],
    SortedGuesses =
	lists:sort(
	  [{hard(NewM),NewM}
	   || NewM <- Ms,
	      not is_exit(NewM)]),
    [G || {_,G} <- SortedGuesses].

update_element(M,I,J,G) ->
    update_nth(I,update_nth(J,G,lists:nth(I,M)),M).

update_nth(I,X,Xs) ->
    {Pre,[_|Post]} = lists:split(I-1,Xs),
    Pre++[X|Post].

%% prop_update() ->
%%     ?FORALL(L,list(int()),
%% 	    ?IMPLIES(L/=[],
%% 		     ?FORALL(I,choose(1,length(L)),
%% 			     update_nth(I,lists:nth(I,L),L) == L))).

%% solve a puzzle

solve(M) ->
    % Solution = solve_refined(refine(fill(M))),
    Solution = solve_refined(refine_par(fill(M))),
    % Solution = solve_refined(refine_all_par(5,fill(M))),
    case valid_solution(Solution) of
	true ->
	    Solution;
	false ->
	    exit({invalid_solution,Solution})
    end.



solve_refined(M) ->
    case solved(M) of
	true ->
	    M;
	false ->
	    solve_one(guesses(M))
    end.

solve_one([]) ->
    exit(no_solution);
solve_one([M]) ->
    solve_refined(M);
solve_one([M|Ms]) ->
    case catch solve_refined(M) of
	{'EXIT',no_solution} ->
	    solve_one(Ms);
	Solution ->
	    Solution
    end.




%% benchmarks

-define(EXECUTIONS,1).

bm(F) ->
    {T,_} = timer:tc(?MODULE,repeat,[F]),
    T/?EXECUTIONS/1000.

repeat(F) ->
    [F() || _ <- lists:seq(1,?EXECUTIONS)].

benchmarks(Puzzles) ->
    [{Name,bm(fun()->solve(M) end)} || {Name,M} <- Puzzles].
   

benchmarks() ->
  {ok,Puzzles} = file:consult("problems.txt"),
  timer:tc(?MODULE,benchmarks,[Puzzles]).

		      
%% check solutions for validity

valid_rows(M) ->
    lists:all(fun valid_row/1,M).

valid_row(Row) ->
    lists:usort(Row) == lists:seq(1,9).

valid_solution(M) ->
    valid_rows(M) andalso valid_rows(transpose(M)) andalso valid_rows(blocks(M)).


				  		  		  

