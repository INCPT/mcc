To calculate the coefficients for a Biquad low-pass filter, the most common method is the RBJ Audio EQ Cookbook. This method uses a set of intermediate variables to transform your target frequency into the five coefficients ($b_0, b_1, b_2, a_1, a_2$). [1, 2] 
## 1. The Variables
You need three pieces of information to start:

* $f_c$: Cutoff frequency (e.g., 20,000 Hz).
* $f_s$: Sample rate (your oversampled rate, e.g., 176,400 Hz).
* $Q$: Quality factor. For a smooth "Butterworth" response, use 0.707 ($1/\sqrt{2}$). [3, 4] 

## 2. The Calculation Steps
First, calculate the intermediate values $\omega_0$ and $\alpha$:
$$\omega_0 = 2 \pi \frac{f_c}{f_s}$$ $$\alpha = \frac{\sin(\omega_0)}{2Q}$$ 
Then, calculate the raw coefficients: [2] 

* $b_0 = \frac{1 - \cos(\omega_0)}{2}$
* $b_1 = 1 - \cos(\omega_0)$
* $b_2 = \frac{1 - \cos(\omega_0)}{2}$
* $a_0 = 1 + \alpha$
* $a_1 = -2 \cos(\omega_0)$
* $a_2 = 1 - \alpha$

Crucial Step: You must normalize the coefficients by dividing all of them by $a_0$. This ensures $a_0$ becomes $1$, which simplifies the real-time filter math. [5] 
## 3. C implementation Example
Here is how you would implement the calculation in a setup function:

void setup_biquad_lpf(Biquad* b, float fc, float fs, float q) {
    float w0 = 2.0f * M_PI * fc / fs;
    float cos_w0 = cosf(w0);
    float alpha = sinf(w0) / (2.0f * q);

    float a0 = 1.0f + alpha;
    b->b0 = ((1.0f - cos_w0) / 2.0f) / a0;
    b->b1 = (1.0f - cos_w0) / a0;
    b->b2 = ((1.0f - cos_w0) / 2.0f) / a0;
    b->a1 = (-2.0f * cos_w0) / a0;
    b->a2 = (1.0f - alpha) / a0;
}

## Visualizing the Response
A Biquad with $Q=0.707$ creates a sharp drop-off (12dB/octave) while keeping the frequency response flat before the cutoff.
The red dashed line shows the cutoff point. Everything to the right of that line is noise (aliasing) that the filter is actively removing. [6] 
Should we look at how to upsample with zero-stuffing, or are you ready to put this into your main loop?

import math
def calculate_biquad_lpf_coeffs(cutoff, sample_rate, q=0.707):
    # Standard Audio EQ Cookbook formulas
    w0 = 2 * math.pi * cutoff / sample_rate
    cos_w0 = math.cos(w0)
    alpha = math.sin(w0) / (2 * q)

    b0 = (1 - cos_w0) / 2
    b1 = 1 - cos_w0
    b2 = (1 - cos_w0) / 2
    a0 = 1 + alpha
    a1 = -2 * cos_w0
    a2 = 1 - alpha

    # Normalize by a0
    return {
        "b0": b0 / a0,
        "b1": b1 / a0,
        "b2": b2 / a0,
        "a1": a1 / a0,
        "a2": a2 / a0
    }
# Example: 20kHz cutoff at 176.4kHz (44.1k * 4x oversampling)
print(calculate_biquad_lpf_coeffs(20000, 176400))


[1] [https://www.einfochips.com](https://www.einfochips.com/blog/the-impact-of-biquad-filters-on-the-digital-world-from-audio-to-wearables/)
[2] [https://webaudio.github.io](https://webaudio.github.io/Audio-EQ-Cookbook/audio-eq-cookbook.html#:~:text=LPF%20%2814%29%20H%20%28%20s%20%29%20=,%28%20A%20%E2%88%92%201%20%29%20cos%20%E2%81%A1)
[3] [https://www.earlevel.com](https://www.earlevel.com/main/2010/12/20/biquad-calculator/)
[4] [https://www.youtube.com](https://www.youtube.com/watch?v=U3AR1XCkX8k)
[5] [https://github.com](https://github.com/loudifier/Biquad-Cookbook)
[6] [https://www.youtube.com](https://www.youtube.com/watch?v=8IdCYjax5VI&t=5)
