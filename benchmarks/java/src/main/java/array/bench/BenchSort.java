package array.bench;

import static java.lang.System.*;

public abstract class BenchSort {
    private long timer, elapsedTime;

    protected void startTimer() {
        timer = currentTimeMillis();
    }

    protected void endTimer() {
        long newTimer = currentTimeMillis();
        elapsedTime = newTimer - timer;
    }

    public long getElapsedTime() {
        return elapsedTime;
    }

    public abstract void sort(int[] arr);
}
