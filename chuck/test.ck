// make our patch
      SinOsc s => dac;

      // time-loop, in which the osc's frequency is changed every 100 ms
      while( true ) {
          100::ms => now;
          Std.rand2f(20.0, 200.0) => s.freq;
      }
