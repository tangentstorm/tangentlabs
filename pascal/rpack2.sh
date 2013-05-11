function runall() { 
    for PACK in xx D C N 1 2 4 8 16 ; do
	echo ----- PACK$PACK---------
	fpc -v0 -dPACK$PACK rpack2.pas
	./rpack2
	for FILE in rpack2.*.dat ; do
	    echo $FILE 
	    hexdump -vC $FILE
	done
	rm rpack2
    done
}

runall > rpack2.log
less rpack2.log
