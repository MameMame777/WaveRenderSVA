# Waveform Render SVA Enhanced

Render waveforms with [WaveDrom](https://github.com/wavedrom/wavedrom) inside [VSCode](https://code.visualstudio.com/) and generate SystemVerilog Assertions (SVA) from JSON waveform descriptions.

## 🙏 Attribution

This project is a **fork and enhancement** of the excellent [waveform-render-vscode](https://github.com/bmpenuelas/waveform-render-vscode) by **Borja Penuelas (bmpenuelas)**. We extend our gratitude for the solid foundation that made these enhancements possible.

**Features:**
- 🌊 Render timing diagrams from WaveDrom JSON *(original feature)*
- ⚡ Generate SystemVerilog Assertions automatically *(enhanced)*
- 💾 Save generated assertions as .sv files *(new)*
- 🔄 Live preview mode for waveforms *(original feature)*
- ✨ Advanced SVA patterns: variable latency, sequences, prohibitions *(new)*

## Usage

📄 Open a .JSON file containing a WaveDrom waveform, like
```json
{ signal: [
  { name: "clk",         wave: "p.....|..." },
  { name: "Data",        wave: "x.345x|=.x", data: ["head", "body", "tail", "data"] },
  { name: "Request",     wave: "0.1..0|1.0" },
  {},
  { name: "Acknowledge", wave: "1.....|01." }
]}
```

<br>

➡️ click the wave button at the top-right corner

![waveform render vscode button](/media/demo_1.png)

*or*

🎹 Press "`Ctrl+K` followed by `Ctrl+D`", or "`Ctrl+Shift+P` followed by `Waveform Render: Draw`" to **draw** the waveform in your editor

*or*

🔃 Press "`Ctrl+K` followed by `Ctrl+L`", or "`Ctrl+Shift+P` followed by `Waveform Render: Toggle Live Preview`" to make the waveform update as you type

<br>

🌈 and you will get a new tab with a nice waveform rendered inside your text editor

![waveform render vscode example](/media/demo_0.png)

## ⚡ SystemVerilog Assertion Generation

**NEW FEATURE**: Generate SystemVerilog assertions from your WaveDrom JSON files!

🔧 Press "`Ctrl+K` followed by `Ctrl+S`", or "`Ctrl+Shift+P` followed by `Waveform Render: Generate SystemVerilog Assertions`" to generate SVA code

📁 The generated assertions will be displayed in a new panel and can be saved as a `.sv` file

**Generated assertions include:**
- Clock signal patterns
- Data transition assertions  
- Signal stability properties
- Request/acknowledge handshake patterns

Example generated output:
```systemverilog
// SystemVerilog Assertions generated from WaveDrom JSON
module assertion_module;
  
  // Assertion for signal: clk
  property clk_clock_p;
    @(posedge clk) $rose(clk) |=> $fell(clk);
  endproperty
  clk_clock_a: assert property(clk_clock_p);

  // Assertion for signal: Request
  property Request_transition_p;
    @(posedge clk) $rose(Request) |-> ##1 $stable(Request);
  endproperty
  Request_transition_a: assert property(Request_transition_p);

endmodule
```

## 💾 Saving the waveform

- You can save the rendered waveform as PNG or SVG by right-clicking the waveform and selecting your preferred format.
- Or click the `📋copy to clipboard` button in twe waveform pannel to copy the image to your clipboard.
- Or use VSCode commands to save as PNG/SVG:
    - `Waveform Render: Copy Save as PNG` (`waveformRender.saveAsPng`)
    - `Waveform Render: Copy Save as SVG` (`waveformRender.saveAsSvg`)

<br>

## Syntax

You can find the complete WaveDrom syntax [in the WaveDrom schema docs](https://github.com/wavedrom/schema/blob/master/WaveJSON.md).
