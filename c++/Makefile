CPP=clang++
CPP=g++ -g
CUDD=~/ver/cudd
CUDDLS=$(CUDD)/obj/libobj.a  \
       $(CUDD)/cudd/libcudd.a \
       $(CUDD)/mtr/libmtr.a \
       $(CUDD)/util/libutil.a \
       $(CUDD)/st/libst.a \
       $(CUDD)/epd/libepd.a



bdd-run: shabdd
	./shabdd

shabdd: shacudd.cc
	$(CPP) -c shacudd.cc -o shabdd.o -I $(CUDD)/include/
	$(CPP) -o shabdd shabdd.o $(CUDDLS)


zdd-run: shazdd
	./shazdd

shazdd: shacudd.cc
	$(CPP) -DUSEZDDS -c shacudd.cc -o shazdd.o -I $(CUDD)/include/
	$(CPP) -o shazdd shazdd.o $(CUDDLS)

clean:
	rm -f shazdd shabdd *.o
