%% This is the application resource file (.app file) for the 'base'
%% application.
{application, log4erl,
[{description, "Logger for erlang in the spirit of Log4J"},
 {vsn, "0.9.0"},
 {modules, [log4erl]},
 {registered,[log4erl]},
 {applications, [kernel,stdlib]},
 {mod, {log4erl,[]}},
 {start_phases, []}
]}.
