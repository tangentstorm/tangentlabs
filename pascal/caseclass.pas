{$mode objfpc}
unit caseclass;
interface uses classes;

  type

    kinds = ( kINT, kSYM, kSTR, kREF, kNUL, kOBJ );

    RNode = record case kind : kinds of  // valid pascal code
	      kINT : ( int : integer );
	      kSYM : ( sym : string );
	      kSTR : ( str : string );
	      kREF : ( ref : TObject );
	      kNUL : ( ptr : TObject );
	      kOBJ : ( obj : TObject );
	    end;

    ONode = object case kind : kinds of   // not allowed
	      kINT : ( int : integer );
	      kSYM : ( sym : string );
	      kSTR : ( str : string );
	      kREF : ( ref : TObject );
	      kNUL : ( ptr : TObject );
	      kOBJ : ( obj : TObject );
	    end;

    CNode = class case kind : kinds of   // not allowed
	      kINT : ( int : integer );
	      kSYM : ( sym : string );
	      kSTR : ( str : string );
	      kREF : ( ref : TObject );
	      kNUL : ( ptr : TObject );
	      kOBJ : ( obj : TObject );
	    end;

implementation
end.

