In a functional DSP context, polyphase upsampling is the mirror image of the decimation process. While decimation sums multiple high-rate samples into one low-rate sample, upsampling takes one low-rate sample and produces a sequence of $M$ high-rate outputs. [1] 
## The Upsampling Setup (Factor 8)
The "monolithic" approach is highly efficient here because it avoids the literal insertion of zeros. Instead, it treats each branch of the polyphase filter as a different "view" of the same input sample.

   1. Shared Delay Line: A single low-rate delay line holds the history of input samples $x[n], x[n-1], \dots$.
   2. Parallel Phase Filters: Eight smaller filters ($P_0$ to $P_7$) process the same delay line simultaneously.
   3. Output Commutator: A high-rate "switch" cycles through the outputs of these eight filters.

C-style Pseudo-code:
This logic produces 8 high-rate samples for every 1 input sample.

// Each phase P[m] is a subset of the original large filter's tapsfloat P[8][8]; // 8 phases, each with 8 taps (for a 64-tap total filter)float state[8]; // A single low-rate delay line shared by all phases
void polyphase_upsample_8x(float input, float* output_block_of_8) {
    // 1. Update the shared low-rate delay line once
    update_delay_line(state, input);

    // 2. Generate 8 different outputs (phases) from that one input
    for (int m = 0; m < 8; ++m) {
        float phase_out = 0.0f;
        for (int k = 0; k < 8; ++k) {
            // Each phase uses the same input state but different coefficients
            phase_out += state[k] * P[m][k];
        }
        // These are your high-rate samples (0 to 7)
        output_block_of_8[m] = phase_out;
    }
}

------------------------------
## Sinc Upsampling Interpolator
A Sinc Interpolator is considered the "ideal" mathematical way to upsample a signal without adding any distortion. [2] 
## The Concept
According to the Whittaker-Shannon interpolation formula, a band-limited signal can be perfectly reconstructed by summing shifted and scaled sinc functions ($\text{sinc}(x) = \frac{\sin(\pi x)}{\pi x}$) centered at each sample point. [3, 4] 

* The "Brick-Wall": In the frequency domain, the sinc function acts as a perfect "brick-wall" low-pass filter that removes all spectral images created during upsampling.
* Zero-Crossing Property: A key feature of the sinc function is that it equals $1$ at $x=0$ and $0$ at all other integer points. This ensures that the original sample values remain unchanged at their original time positions after interpolation. [4, 5] 

## Practical Implementation: Windowed Sinc
Because a true sinc function extends infinitely in both directions, real-time DSP uses a Windowed Sinc. [5, 6] 

* The sinc curve is "cut off" after a certain number of samples (the "points" or "taps") and multiplied by a windowing function (like a Hanning or Kaiser window) to prevent abrupt edges that cause ringing artifacts.
* When you see a "32-point sinc" in a DAW, it means the interpolator is using 32 neighboring samples to calculate the value of each new "in-between" sample. [5, 6, 7] 

## Why use it in a Monolithic Primitive?
A monolithic oversample primitive can automatically design an optimal windowed sinc filter based on the factor $M$. It handles the math of splitting that sinc curve into the polyphase branches ($P_0 \dots P_7$) so the user gets "perfect" reconstruction without needing to know Fourier theory. [8, 9] 
Would you like to see how the windowing function changes the quality of the interpolation in a frequency plot?
------------------------------

[1] [https://www.youtube.com](https://www.youtube.com/watch?v=9RzJ6N8Xu4Q&t=105)
[2] [https://la.mathworks.com](https://la.mathworks.com/matlabcentral/fileexchange/59027-time-domain-sinc-interpolation-resampling?tab=discussions)
[3] [https://en.wikipedia.org](https://en.wikipedia.org/wiki/Whittaker%E2%80%93Shannon_interpolation_formula)
[4] [https://math.stackexchange.com](https://math.stackexchange.com/questions/1372632/how-does-sinc-interpolation-work)
[5] [https://therationalaudiophile.wordpress.com](https://therationalaudiophile.wordpress.com/2018/02/22/how-to-re-sample-a-signal/)
[6] [https://dsp.stackexchange.com](https://dsp.stackexchange.com/questions/69058/how-to-implement-sinc-interpolation)
[7] [https://www.sciencedirect.com](https://www.sciencedirect.com/topics/engineering/sinc-interpolation)
[8] [https://www.youtube.com](https://www.youtube.com/watch?v=5Pmk55tPLw4&t=1)
[9] [https://www.mathworks.com](https://www.mathworks.com/help/dsp/ref/firinterpolation.html)

The core difference is that Sinc Interpolation describes the mathematical shape of the filter, while Polyphase Decomposition describes the efficient data structure used to run it.
In a functional DSP engine, when you call oversample(8, f, g), the compiler calculates a Sinc window, then splits it into Polyphase branches.
## 1. Sinc Interpolation (Mathematical Logic)
This is the "naive" way to think about it: for every new high-rate point, you look at all nearby original samples and weigh them by their distance on a Sinc curve.

// The "Ideal" Sinc function
float sinc(float x) {
    if (x == 0) return 1.0f;
    float pi_x = 3.14159f * x;
    return sin(pi_x) / pi_x;
}

// To get a high-rate sample at fractional position 't' (e.g., 0.125, 0.25...)
float get_sinc_interpolated_sample(float t, float* low_rate_buffer) {
    float result = 0.0f;
    int window_size = 16; // Number of neighboring samples to look at

    for (int i = -window_size; i <= window_size; i++) {
        // Weight the sample by its distance from the target 't'
        float weight = sinc(t - i) * window(i); 
        result += low_rate_buffer[i] * weight;
    }
    return result;
}

## 2. Comparison: Sinc vs. Polyphase

| Feature | Sinc Interpolation (Concept) | Polyphase Upsampling (Execution) |
|---|---|---|
| What it is | The Filter Kernel (The "What"). | The Algorithm (The "How"). |
| Logic | Uses a continuous function to find "in-between" values. | Uses pre-calculated, fixed filter branches. |
| CPU Cost | High (lots of sin() calls or large lookups). | Very Low (standard dot-products). |
| Data Flow | One output at a time. | Generates all $M$ phases in one burst. |

## 3. How the Monolithic Approach Marries Them
A compiler like Cmajor or Faust doesn't run the sinc() function in real-time. Instead, it "bakes" the Sinc into the Polyphase structure at compile-time:

   1. Design: It samples the Sinc function at intervals of $1/M$.
   2. Decompose: It takes those samples and assigns them to the $P_0...P_7$ branches.
   3. Execute: The resulting code looks exactly like the Polyphase Upsample code from the previous turn, but the coefficients ($P[m][k]$) are specifically chosen to match the Sinc curve.

## Why this matters for your primitive design:
If you provide separate primitives, the user has to design their own filter coefficients to ensure they are using a Sinc shape. If you provide a monolithic primitive, the compiler guarantees that the coefficients are a perfect Sinc window, ensuring the highest possible audio fidelity with the lowest CPU hit.
Would you like to see how windowing (like Kaiser or Lanczos) is applied to the Sinc coefficients to prevent "ringing" in the audio?
