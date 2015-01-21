-module(xml_appender).

-behaviour(gen_event).

-include("../include/log4erl.hrl").
-include_lib("kernel/include/file.hrl").

-import(log4erl_utils, [to_list/1, to_atom/1, to_int/1]).

%% gen_event callbacks
-export([init/1, handle_event/2, handle_call/2,
     handle_info/2, terminate/2, code_change/3]).

-define(FLOAT_BIAS, 1022).
-define(MIN_EXP, -1074).
-define(BIG_POW, 4503599627370496).

-define(DEFAULT_XMLSPEC, [{level, "%L", att},
              {date, "%j", att},
              {time, "%T", att},
              {message, "%l", elem}]).

%% xmlspec is a list of xml_spec records
-record(xml_appender, {dir, file_name, fd, counter, log_type, rotation, suffix="xml", level, xmlspec}).

%% xmlspec is of the form {Name, Format, Type}
%% where Name is the name of the element or attribute
%% Format is the format of the value
%% Type is either 'att' or 'elem'
-record(xml_spec, {name, format, type}).

%%======================================
%% gen_event callback functions
%%======================================
init({conf, Conf}) when is_list(Conf) ->
    CL = lists:foldl(fun(X, List) ->
                 case X of
                 {X1, D} ->
                     [proplists:get_value(X1,Conf,D)|List];
                 _ ->
                     [proplists:get_value(X,Conf)|List]
                 end
             end,
             [],
             [dir, file, type, max, rotation, suffix, level, {xmlspec, ?DEFAULT_XMLSPEC}]),

    init(list_to_tuple(lists:reverse(CL)));
init({Dir, Fname, {Type, Max}, Rot, Suf, Level, Spec} = _Conf) ->
    ?LOG2("xml_appender:init() - 1 ~p~n",[_Conf]),
    File = Dir ++ "/" ++ Fname ++ "." ++ Suf,
    Ltype = #log_type{type = Type, max = Max},
    % Check Rot >= 0
    Rot1 = case Rot < 0 of
           true ->
           0;
           false ->
           Rot
       end,
    {ok, Fd} = file:open(File, ?FILE_OPTIONS),

    %% Translate {Name, Format, Type} to #xml_spec records
    XmlSpec = lists:map(fun({N, F, T}) ->
                {ok, Tokens} = log_formatter:parse(F),
                #xml_spec{name=N, format=Tokens, type=T}
            end, Spec),

    %% Start xml 
    file:write(Fd, "<?xml>\n<log4erl>"),

    State = #xml_appender{dir = Dir, file_name = Fname, fd = Fd, counter=0,
               log_type = Ltype, rotation = Rot1, suffix=Suf,
               level=Level, xmlspec=XmlSpec},
    ?LOG2("xml_appender:init() with conf ~p~n",[State]),
    {ok, State};
% These 2 are for result of reading conf file
init({Dir, Fname, Type, Max, Rot, Suf, Level, Spec}) ->
    init({to_list(Dir), to_list(Fname), {to_atom(Type), to_int(Max)}, to_int(Rot), to_list(Suf), to_atom(Level), Spec}).

handle_event({change_level, Level}, State) ->
    State2 = State#xml_appender{level = Level},
    ?LOG2("Changed level to ~p~n",[Level]),
    {ok, State2};
handle_event({log,LLog}, State) ->
    ?LOG2("handl_event:log = ~p~n",[LLog]),
    do_log(LLog, State),
    Res = check_rotation(State),
    {ok, Res}.

handle_call({change_format, _Format}, State) ->
    ?LOG("Cannot change format in xml_appender~n"),
    {ok, ok, State};
handle_call({change_level, Level}, State) ->
    State2 = State#xml_appender{level = Level},
    ?LOG2("Changed level to ~p~n",[Level]),
    {ok, ok, State2};
handle_call(_Request, State) ->
    Reply = ok,
    {ok, Reply, State}.

handle_info(_Info, State) ->
    ?LOG2("~w received unknown message: ~p~n", [?MODULE, _Info]),
    {ok, State}.

terminate(_Reason, #xml_appender{fd=Fd}) ->
    file:write(Fd, "</log4erl>\n"),
    ok.

code_change(_OldVsn, State, _Extra) ->
    {ok, State}.

%%======================================
%% internal callback functions
%%======================================
do_log(#log{level = L} = Log,#xml_appender{fd = Fd, level=Level, xmlspec=XmlSpec} = _State) when is_atom(L) ->
    ToLog = log4erl_utils:to_log(L, Level),
    case ToLog of
    true ->
        M = format_xml(Log, XmlSpec),
        file:write(Fd, M);
    false ->
        ok
    end;
do_log(_Other, _State) ->
    ?LOG2("unknown level ~p~n",[_Other]),
    ok.

rotate(#xml_appender{fd = Fd, dir=Dir,  file_name=Fn, counter=Cntr, rotation=Rot, suffix=Suf} = S) ->
    file:write(Fd, "</log4erl>\n"),
    file:close(Fd),
    ?LOG("Starting rotation~n"),
    C = if
        Rot == 0 ->
        0;
        Cntr >= Rot ->
        1;
        true ->
        Cntr+1
    end,
    Src = Dir ++ "/" ++ Fn ++ "." ++ Suf,
    Fname = case C of
        0 ->
            Dir ++ "/" ++ Fn ++ "." ++ Suf;
        _ ->
            Dir ++ "/" ++ Fn ++ "_" ++ integer_to_list(C) ++ "." ++ Suf
        end,
    ?LOG2("Renaming file from ~p to ~p~n",[Src, Fname]),
    file:rename(Src, Fname),
    {ok ,Fd2} = file:open(Src, ?FILE_OPTIONS_ROTATE),
    file:write(Fd2, "<?xml>\n<log4erl>"),
    State2 = S#xml_appender{dir = Dir, file_name = Fn, fd = Fd2, rotation = Rot, suffix=Suf},
    {ok, State2}.

% Check if the file needs to be rotated
% ignore in case of if log type is set to time instead of size        
check_rotation(State) ->
    #xml_appender{dir=Dir, file_name=Fname, log_type = #log_type{type=T, max=Max}, suffix=Suf} = State,
    case T of
    size ->
        File = Dir ++ "/" ++ Fname ++  "." ++ Suf,
        {ok, Finfo} = file:read_file_info(File),
        Size = Finfo#file_info.size,
        if
        Size > Max ->
            {ok, State2} = rotate(State),
            State2;
        true ->
            State
        end;
    %% time-based rotation is not implemented yet
    _ ->
        State
    end.

format_xml(Log, Spec) ->
    Att = lists:filter(fun(#xml_spec{type=T}) ->
                   T == att
               end,
               Spec),
    Elems = lists:filter(fun(#xml_spec{type=T}) ->
                 T == elem
             end,
             Spec),

    A = attributes(Log, Att),
    B = elements(Log, Elems),

    "<log" ++ A ++ ">\n" ++ B ++ "</log>\n".

attributes(_, []) ->
    [];
attributes(Log, Atts) ->
    attributes(Log, Atts, []).

attributes(_, [], Acc) ->
    lists:reverse(Acc);
attributes(Log, [#xml_spec{name=N,format=F}|Rest], Acc) ->
    S = " " ++ escape_attr(log4erl_utils:to_list(N)) ++ "=\"" ++ escape_attr(log_formatter:format(Log, F)) ++"\"",
    attributes(Log, Rest, [S|Acc]).

elements(_, []) ->
    [];
elements(Log, Elems) ->
    elements(Log, Elems, []).

elements(_, [], Acc) ->
    lists:reverse(Acc);
elements(Log, [#xml_spec{name=N, format=F}|Rest], Acc) ->
    Name = escape_attr(log4erl_utils:to_list(N)),
    L = lists:flatten(log_formatter:format(Log, F)),
    S = "\t<" ++ Name ++ ">" ++ escape(L) ++"</" ++ Name ++ ">\n",
    elements(Log, Rest, [S|Acc]).

%% The following code is copied/pasted from mochiweb's 'mochiweb_html' & 'mochinum' modules
%% See http://code.google.com/p/mochiweb

%% @spec escape(string() | atom() | binary()) -> binary()
%% @doc Escape a string such that it's safe for HTML (amp; lt; gt;).
escape(B) when is_binary(B) ->
    escape(binary_to_list(B), []);
escape(A) when is_atom(A) ->
    escape(atom_to_list(A), []);
escape(S) when is_list(S) ->
    escape(S, []).

%% @spec escape_attr(string() | binary() | atom() | integer() | float()) -> binary()
%% @doc Escape a string such that it's safe for HTML attrs
%%      (amp; lt; gt; quot;).
escape_attr(B) when is_binary(B) ->
    escape_attr(binary_to_list(B), []);
escape_attr(A) when is_atom(A) ->
    escape_attr(atom_to_list(A), []);
escape_attr(S) when is_list(S) ->
    escape_attr(S, []);
escape_attr(I) when is_integer(I) ->
    escape_attr(integer_to_list(I), []);
escape_attr(F) when is_float(F) ->
    escape_attr(digits(F), []).

escape([], Acc) ->
    lists:reverse(Acc);
escape("<" ++ Rest, Acc) ->
    escape(Rest, lists:reverse("&lt;", Acc));
escape(">" ++ Rest, Acc) ->
    escape(Rest, lists:reverse("&gt;", Acc));
escape("&" ++ Rest, Acc) ->
    escape(Rest, lists:reverse("&amp;", Acc));
escape([C | Rest], Acc) ->
    escape(Rest, [C | Acc]).

-define(QUOTE, $\").

escape_attr([], Acc) ->
    lists:reverse(Acc);
escape_attr("<" ++ Rest, Acc) ->
    escape_attr(Rest, lists:reverse("&lt;", Acc));
escape_attr(">" ++ Rest, Acc) ->
    escape_attr(Rest, lists:reverse("&gt;", Acc));
escape_attr("&" ++ Rest, Acc) ->
    escape_attr(Rest, lists:reverse("&amp;", Acc));
escape_attr([?QUOTE | Rest], Acc) ->
    escape_attr(Rest, lists:reverse("&quot;", Acc));
escape_attr([C | Rest], Acc) ->
    escape_attr(Rest, [C | Acc]).

%% The foolowing is cut from mochiweb repo, mochinum:digit/1
digits(N) when is_integer(N) ->
    integer_to_list(N);
digits(0.0) ->
    "0.0";
digits(Float) ->
    {Frac1, Exp1} = frexp_int(Float),
    [Place0 | Digits0] = digits1(Float, Exp1, Frac1),
    {Place, Digits} = transform_digits(Place0, Digits0),
    R = insert_decimal(Place, Digits),
    case Float < 0 of
        true ->
            [$- | R];
        _ ->
            R
    end.

%% @spec int_pow(X::integer(), N::integer()) -> Y::integer()
%% @doc  Moderately efficient way to exponentiate integers.
%%       int_pow(10, 2) = 100.
int_pow(_X, 0) ->
    1;
int_pow(X, N) when N > 0 ->
    int_pow(X, N, 1).

%% @spec int_ceil(F::float()) -> integer()
%% @doc  Return the ceiling of F as an integer. The ceiling is defined as
%%       F when F == trunc(F);
%%       trunc(F) when F &lt; 0;
%%       trunc(F) + 1 when F &gt; 0.
int_ceil(X) ->
    T = trunc(X),
    case (X - T) of
        Pos when Pos > 0 -> T + 1;
        _ -> T
    end.


%% Internal API

int_pow(X, N, R) when N < 2 ->
    R * X;
int_pow(X, N, R) ->
    int_pow(X * X, N bsr 1, case N band 1 of 1 -> R * X; 0 -> R end).

insert_decimal(0, S) ->
    "0." ++ S;
insert_decimal(Place, S) when Place > 0 ->
    L = length(S),
    case Place - L of
         0 ->
            S ++ ".0";
        N when N < 0 ->
            {S0, S1} = lists:split(L + N, S),
            S0 ++ "." ++ S1;
        N when N < 6 ->
            %% More places than digits
            S ++ lists:duplicate(N, $0) ++ ".0";
        _ ->
            insert_decimal_exp(Place, S)
    end;
insert_decimal(Place, S) when Place > -6 ->
    "0." ++ lists:duplicate(abs(Place), $0) ++ S;
insert_decimal(Place, S) ->
    insert_decimal_exp(Place, S).

insert_decimal_exp(Place, S) ->
    [C | S0] = S,
    S1 = case S0 of
             [] ->
                 "0";
             _ ->
                 S0
         end,
    Exp = case Place < 0 of
              true ->
                  "e-";
              false ->
                  "e+"
          end,
    [C] ++ "." ++ S1 ++ Exp ++ integer_to_list(abs(Place - 1)).


digits1(Float, Exp, Frac) ->
    Round = ((Frac band 1) =:= 0),
    case Exp >= 0 of
        true ->
            BExp = 1 bsl Exp,
            case (Frac =/= ?BIG_POW) of
                true ->
                    scale((Frac * BExp * 2), 2, BExp, BExp,
                          Round, Round, Float);
                false ->
                    scale((Frac * BExp * 4), 4, (BExp * 2), BExp,
                          Round, Round, Float)
            end;
        false ->
            case (Exp =:= ?MIN_EXP) orelse (Frac =/= ?BIG_POW) of
                true ->
                    scale((Frac * 2), 1 bsl (1 - Exp), 1, 1,
                          Round, Round, Float);
                false ->
                    scale((Frac * 4), 1 bsl (2 - Exp), 2, 1,
                          Round, Round, Float)
            end
    end.

scale(R, S, MPlus, MMinus, LowOk, HighOk, Float) ->
    Est = int_ceil(math:log10(abs(Float)) - 1.0e-10),
    %% Note that the scheme implementation uses a 326 element look-up table
    %% for int_pow(10, N) where we do not.
    case Est >= 0 of
        true ->
            fixup(R, S * int_pow(10, Est), MPlus, MMinus, Est,
                  LowOk, HighOk);
        false ->
            Scale = int_pow(10, -Est),
            fixup(R * Scale, S, MPlus * Scale, MMinus * Scale, Est,
                  LowOk, HighOk)
    end.

fixup(R, S, MPlus, MMinus, K, LowOk, HighOk) ->
    TooLow = case HighOk of
                 true ->
                     (R + MPlus) >= S;
                 false ->
                     (R + MPlus) > S
             end,
    case TooLow of
        true ->
            [(K + 1) | generate(R, S, MPlus, MMinus, LowOk, HighOk)];
        false ->
            [K | generate(R * 10, S, MPlus * 10, MMinus * 10, LowOk, HighOk)]
    end.

generate(R0, S, MPlus, MMinus, LowOk, HighOk) ->
    D = R0 div S,
    R = R0 rem S,
    TC1 = case LowOk of
              true ->
                  R =< MMinus;
              false ->
                  R < MMinus
          end,
    TC2 = case HighOk of
              true ->
                  (R + MPlus) >= S;
              false ->
                  (R + MPlus) > S
          end,
    case TC1 of
        false ->
            case TC2 of
                false ->
                    [D | generate(R * 10, S, MPlus * 10, MMinus * 10,
                                  LowOk, HighOk)];
                true ->
                    [D + 1]
            end;
        true ->
            case TC2 of
                false ->
                    [D];
                true ->
                    case R * 2 < S of
                        true ->
                            [D];
                        false ->
                            [D + 1]
                    end
            end
    end.

unpack(Float) ->
    <<Sign:1, Exp:11, Frac:52>> = <<Float:64/float>>,
    {Sign, Exp, Frac}.

transform_digits(Place, [0 | Rest]) ->
    transform_digits(Place, Rest);
transform_digits(Place, Digits) ->
    {Place, [$0 + D || D <- Digits]}.


frexp_int(F) ->
    case unpack(F) of
        {_Sign, 0, Frac} ->
            {Frac, ?MIN_EXP};
        {_Sign, Exp, Frac} ->
            {Frac + (1 bsl 52), Exp - 53 - ?FLOAT_BIAS}
    end.
