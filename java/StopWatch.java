import java.util.ArrayList;

/**
 * A simple stopwatch that can calculate the average time.
 * @author michal
 */
public class StopWatch {
    
    private final ArrayList<Long> _times = new ArrayList<>();
    private boolean _running;
    private long _startTime;
    
    public void clear() {
        _times.clear();
    }
    
    public void start() {
        assert _running : "timer is already started.";
        _startTime = System.nanoTime();
        _running = true;
    }
    
    public void stop() {
        assert ! _running : "timer is not running.";
        _times.add(System.nanoTime() - _startTime);
        _running = false;
    }
    
    public double averageTimeMillis() {
        double result = 0;
        if (_times.size() > 0) {
            for (long time : _times) result += time;
            result /= _times.size();
        }
        return result;
    }
    
}
