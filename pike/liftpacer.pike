
// #import SDL;


static SDL.Event event = SDL.Event();




void lifterbot() {


  array reps = ({ ({12,5}), ({10,6}), ({8,6}), ({6,7}), ({12,9}), ({12,10})});

  foreach(reps; int set; reps) {
    write("set %d : %d reps @ %d\n", set+1, reps[0], reps[1]);
  }

  write("do the lift");


}









int main() {
  SDL.init(SDL.INIT_VIDEO | SDL.INIT_AUDIO);
  SDL.set_video_mode(800, 600, 24, 0);


  lifterbot();

  /*
  while (event->wait()) {
    switch (event->type) {
    case SDL.QUIT:
      return 0;
      break;
    }
  }
  */

}
