// sound file

"w:/app/lucid/thisisadream.wav"=> string filename;
//"w:/app/lucid/13-lucid-hand.mp3"=> string filename;
//if( me.args() ) me.arg(0) => filename;

// the patch 
SndBuf buf => dac;

SinOsc s => dac;

// load the file
filename => buf.read;

10000::ms => now;

// time loop
//while( true )
//{
    //0 => buf.pos;
    //Std.rand2f(.2,.9) => buf.gain;
    //Std.rand2f(.5,1.5) => buf.rate;
	
//}
