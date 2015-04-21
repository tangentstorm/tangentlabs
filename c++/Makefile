CPP=clang++
CPP=g++ -g
CUDD=~/ver/cudd
CUDDLS=$(CUDD)/obj/libobj.a  \
       $(CUDD)/cudd/libcudd.a \
       $(CUDD)/mtr/libmtr.a \
       $(CUDD)/util/libutil.a \
       $(CUDD)/st/libst.a \
       $(CUDD)/epd/libepd.a

shacudd-run: shacudd
	./shacudd

shacudd: shacudd.o
	$(CPP) -o shacudd shacudd.o $(CUDDLS)

shacudd.o: shacudd.cc
	$(CPP) -c shacudd.cc -I $(CUDD)/include/
