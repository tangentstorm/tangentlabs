###################################################
#
# osql.tcl  - an odbc/sql client in tcl
#
#             by michal wallace
#                sabren@manifestation.com
#
#             requires tclodbc.dll, available on
#             the web from... ??????????????????
#
#             (c)1999 me.. all rights reserved,
#             but I really don't care what you 
#             do with this. :)
#
###################################################
# version history 
###################################################
# 0.1 - 0526.1999 - initial version
###################################################

##[ packages ]#####################################
package require tclodbc

##[ variables ]####################################
set fullcmd "" ;# entire commandline as string
set cmd     "" ;# first word of command line
set args    "" ;# arguments to the command
set db      "" ;# main database object
set st      "" ;# statement object


##[ procedures ]###################################


if { $errorCode > 0 } then { puts "error is: $errorCode"  }

# help screen
proc help {} {
	puts "-----------------------------------------"
	puts "acceptable commands:"
	puts ""
	puts "   help   ... help"
	puts "   open   ... open a database connection"
	puts "   show   ... show dsns, tables, etc "
	puts "   quit   ... quit the program "
	puts "   exit   ... quit the program "
	puts ""
	puts " (all sql statements are allowed) "
	puts "-----------------------------------------"
}

# the "show" command
proc show {what} {
	switch $what {
		"dsns"    list_dsns
		"tables"  list_tables
	}
}

# list DSNs for "show"
proc list_dsns {} { 
	set dsns [database datasources]
	foreach dsn $dsns {
		puts $dsn
	}
}

# list tables for "show"
proc list_tables {} {
	set tbls [db tables]
	foreach tbl $tbls {
		puts [lindex $tbl 2]
	}
}

# open connection to a dsn
proc open_dsn {dsn user pass} {
	set err [catch {database db $dsn $user $pass}]
	if {$err != 0} then { 
		puts "couldn't open $dsn" 
	} else {
		puts "OK"
	}
}


# actually run the sql 
proc sql_statement {statement} {
	global errorInfo

	set err [catch {set result [db $statement]}]
	if {$err > 0 } then {
		puts $errorInfo
	} else {
		puts $result
	}
}

# ..or a query
proc sql_query {query} {
	set rs ""
	set rs [db $query]
	foreach rec $rs {
		puts $rec
	}
}

##[ main code ]####################################

puts "-----------------------------------------"
puts "osql - odbc sql shell"
puts "by michal wallace"
puts "-----------------------------------------"

while {$cmd != "exit"} {

	## first read the input
	puts -nonewline ":" 
	flush stdout ;# why doesn't this flush by itself?
	gets stdin fullcmd


	## break it into a list
	set args [split $fullcmd]
	set cmd  [lindex $args 0]


	## now do something about it
	switch $cmd {
		
		"open"  {open_dsn [lindex $args 1] [lindex $args 2] [lindex $args 3]}
		"show"  {show [lindex $args 1]}
		"exit"  {}
		"quit"  {set cmd "exit"}
		"help"  {help}
		
		"select"   {sql_query $fullcmd}

		"insert"   {sql_statement $fullcmd}
		"describe" {sql_statement $fullcmd}
		"update"   {sql_statement $fullcmd}
		"delete"   {sql_statement $fullcmd}
		"create"   {sql_statement $fullcmd}
		"alter"    {sql_statement $fullcmd}
		"drop"     {sql_statement $fullcmd}

		default {puts "invalid command - use 'help' for a list of commands" }
	}
}

puts "bye!"


## END ##