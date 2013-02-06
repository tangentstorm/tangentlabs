// http://www.iua.upf.es/~gcoleman/chuck/tutorial/tutorial.html

//connect a plucked string to the soundcard out
StifKarp inst => dac;
StifKarp inst2 => dac;

inst2.noteOn(0.5);
1::second =>now; 

// mtof = midi to freq

Std.mtof( 60 ) => inst.freq; //set the note to middle-C
inst.noteOn( 0.5 ); //play a note at half volume
1::second => now; //compute audio for 1 second

[0,2,3,1,4,2,6,3,4,4] @=> int mel[]; //sequence data

for (0=>int i; ; i++) { //infinite loop
  std.mtof( 48 + mel[i%mel.cap()] ) => inst.freq; //set the note
  inst.noteOn( 0.5 ); //play a note at half volume
  300::ms => now; //compute audio for 0.3 sec
}
