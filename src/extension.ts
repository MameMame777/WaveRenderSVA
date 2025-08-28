import * as path from "path";
import * as vscode from 'vscode';

export function activate(context: vscode.ExtensionContext) {
  // Start and live preview mode
  context.subscriptions.push(
    vscode.commands.registerCommand("waveformRender.start", () => {
      WaveformRenderPanel.disableLivePreview();
      vscode.window.showInformationMessage(
        "Waveform refreshed manually, Live Preview OFF"
      );
      WaveformRenderPanel.createOrShow(context.extensionPath);
    })
  );
  context.subscriptions.push(
    vscode.commands.registerCommand("waveformRender.toggleLivePreview", () => {
      WaveformRenderPanel.toggleLivePreview(context.extensionPath);
    })
  );

  // Add listener for changing active text editor
  context.subscriptions.push(
    vscode.window.onDidChangeActiveTextEditor((editor) => {
      if (
        WaveformRenderPanel.livePreview &&
        editor &&
        (editor.document.fileName.toLowerCase().endsWith(".json") ||
          editor.document.fileName.toLowerCase().endsWith(".json5"))
      ) {
        WaveformRenderPanel.createOrShow(context.extensionPath);
      }
    })
  );

  // Export the waveform
  context.subscriptions.push(
    vscode.commands.registerCommand("waveformRender.saveAsPng", () => {
      WaveformRenderPanel.saveAsPng();
    })
  );
  context.subscriptions.push(
    vscode.commands.registerCommand("waveformRender.saveAsSvg", () => {
      WaveformRenderPanel.saveAsSvg();
    })
  );
  context.subscriptions.push(
    vscode.commands.registerCommand("waveformRender.generateSVA", () => {
      SVAGeneratorPanel.createOrShow(context.extensionPath);
    })
  );
}

function getFilename() {
  return vscode.window.activeTextEditor.document.fileName
    .split(/[\\/]/)
    .pop()
    .replace(/\.json5?$/i, "");
}

function getTitle() {
  return "Waveform: " + getFilename();
}

/**
 * Manages webview panel
 */
class WaveformRenderPanel {
  /**
   * Track the currently panel. Only allow a single panel to exist at a time.
   */
  public static currentPanel: WaveformRenderPanel | undefined;

  public static livePreview: boolean = false;
  public static livePreviewDocumentPath;
  public static listenerTextChange;

  public static readonly viewType = "waveformRender";

  private readonly _panel: vscode.WebviewPanel;
  private readonly _extensionPath: string;
  private _disposables: vscode.Disposable[] = [];

  public static toggleLivePreview(extensionPath: string) {
    const closePanelOnDisable = vscode.workspace
      .getConfiguration("waveformRender")
      .get<boolean>("closePanelOnDisable", true);

    if (WaveformRenderPanel.livePreview) {
      WaveformRenderPanel.disableLivePreview();

      // Close the panel if the setting is enabled
      if (closePanelOnDisable && WaveformRenderPanel.currentPanel) {
        WaveformRenderPanel.currentPanel.dispose();
      }
    } else {
      WaveformRenderPanel.livePreviewDocumentPath =
        vscode.window.activeTextEditor.document.uri.path;
      WaveformRenderPanel.listenerTextChange =
        vscode.workspace.onDidChangeTextDocument(function (event) {
          WaveformRenderPanel.createOrShow(extensionPath);
        });
      WaveformRenderPanel.livePreview = true;
      WaveformRenderPanel.createOrShow(extensionPath);
    }
    vscode.window.showInformationMessage(
      "Waveform Live Preview: " +
        (WaveformRenderPanel.livePreview ? "ON" : "OFF")
    );
  }

  public static disableLivePreview() {
    WaveformRenderPanel.livePreviewDocumentPath = null;
    if (WaveformRenderPanel.listenerTextChange) {
      WaveformRenderPanel.listenerTextChange.dispose();
    }
    WaveformRenderPanel.livePreview = false;
  }

  public static createOrShow(extensionPath: string) {
    const activeEditor = vscode.window.activeTextEditor;

    // Ensure we have an active editor and it's a JSON file
    if (
      !activeEditor ||
      !(
        activeEditor.document.fileName.toLowerCase().endsWith(".json") ||
        activeEditor.document.fileName.toLowerCase().endsWith(".json5")
      )
    ) {
      return;
    }

    // If we already have a panel
    if (WaveformRenderPanel.currentPanel) {
      // Update the panel title
      WaveformRenderPanel.currentPanel._panel.title = getTitle();

      // Update the panel content
      WaveformRenderPanel.currentPanel._updateWithFileContent();
      return;
    }

    // Otherwise, create a new panel.
    const panel = vscode.window.createWebviewPanel(
      WaveformRenderPanel.viewType,
      getTitle(),
      { preserveFocus: true, viewColumn: vscode.ViewColumn.Beside },
      {
        // Enable javascript in the webview
        enableScripts: true,

        // And restrict the webview to only loading content from our extension's `localScripts` directory.
        localResourceRoots: [
          vscode.Uri.file(path.join(extensionPath, "localScripts")),
        ],
      }
    );

    WaveformRenderPanel.currentPanel = new WaveformRenderPanel(
      panel,
      extensionPath
    );
  }

  private constructor(panel: vscode.WebviewPanel, extensionPath: string) {
    this._panel = panel;
    this._extensionPath = extensionPath;

    this._updateWithFileContent();

    // Listen for when the panel is disposed
    // This happens when the user closes the panel or when the panel is closed programatically
    this._panel.onDidDispose(() => this.dispose(), null, this._disposables);

    // Handle messages from the webview
    this._panel.webview.onDidReceiveMessage(
      (message) => {
        switch (message.command) {
          case 'generateSVA':
            SVAGeneratorPanel.createOrShow(this._extensionPath);
            break;
        }
      },
      null,
      this._disposables
    );
  }

  public dispose() {
    WaveformRenderPanel.currentPanel = undefined;

    // Disable live preview when the panel is closed
    WaveformRenderPanel.disableLivePreview();

    // Clean up our resources
    this._panel.dispose();

    while (this._disposables.length) {
      const x = this._disposables.pop();
      if (x) {
        x.dispose();
      }
    }
  }

  public static saveAsSvg() {
    if (WaveformRenderPanel.currentPanel) {
      WaveformRenderPanel.currentPanel._panel.webview.postMessage({
        command: "saveSvg",
      });
    }
  }

  public static saveAsPng() {
    if (WaveformRenderPanel.currentPanel) {
      WaveformRenderPanel.currentPanel._panel.webview.postMessage({
        command: "savePng",
      });
    }
  }

  private _updateWithFileContent() {
    // Get the current text editor
    let editor = vscode.window.activeTextEditor;
    let doc = editor.document;
    let docContent = doc.getText();

    // Set the webview's html content
    this._update(docContent, getFilename());
  }

  private _update(
    fileContents: string = `{ signal: [
    { name: "clk",         wave: "p.....|..." },
    { name: "Data",        wave: "x.345x|=.x", data: ["head", "body", "tail", "data"] },
    { name: "Request",     wave: "0.1..0|1.0" },
    {},
    { name: "Acknowledge", wave: "1.....|01." }
  ]}`,
    title?: string
  ) {
    this._panel.webview.html = this._getHtmlForWebview(fileContents, title);
  }

  private _getHtmlForWebview(
    waveformJson: string,
    title: string = "waveform render"
  ) {
    const scriptPathOnDisk = vscode.Uri.file(
      path.join(this._extensionPath, "localScripts", "wavedrom.min.js")
    );
    const defaultSkinPathOnDisk = vscode.Uri.file(
      path.join(this._extensionPath, "localScripts/skins", "default.js")
    );
    const narrowSkinPathOnDisk = vscode.Uri.file(
      path.join(this._extensionPath, "localScripts/skins", "narrow.js")
    );
    const lowkeySkinPathOnDisk = vscode.Uri.file(
      path.join(this._extensionPath, "localScripts/skins", "lowkey.js")
    );

    // And the uri we use to load this script in the webview
    const scriptUri = this._panel.webview.asWebviewUri(scriptPathOnDisk);
    const defaultUri = this._panel.webview.asWebviewUri(defaultSkinPathOnDisk);
    const narrowUri = this._panel.webview.asWebviewUri(narrowSkinPathOnDisk);
    const lowkeyUri = this._panel.webview.asWebviewUri(lowkeySkinPathOnDisk);

    return `<!DOCTYPE html>
            <html lang="en">
            <head>
                <meta charset="UTF-8">

                  <script src="${scriptUri}"></script>

                  <script src="${defaultUri}"></script>
                  <script src="${narrowUri}"></script>
                  <script src="${lowkeyUri}"></script>

                  <title>${title}</title>
            </head>

            <script>
            const vscode = acquireVsCodeApi();
            
            window.addEventListener('message', async event => {
              const command = event.data.command;

              const svgEl = document.querySelector('svg');
              if (!svgEl) return;

              if (command === 'saveSvg') {
                const blob = new Blob([svgEl.outerHTML], { type: 'image/svg+xml' });
                const url = URL.createObjectURL(blob);
                const a = document.createElement('a');
                a.href = url;
                a.download = document.title + '.svg';
                a.click();
                URL.revokeObjectURL(url);
              }

              if (command === 'savePng') {
                const svg = new XMLSerializer().serializeToString(svgEl);
                const svg64 = btoa(unescape(encodeURIComponent(svg)));
                const img = new Image();
                img.src = 'data:image/svg+xml;base64,' + svg64;

                img.onload = async function () {
                  const scaleFactor = 2; // 2x resolution
                  const canvas = document.createElement('canvas');
                  const width = img.width * scaleFactor;
                  const height = img.height * scaleFactor;

                  canvas.width = width;
                  canvas.height = height;
                  const ctx = canvas.getContext('2d');
                  ctx.scale(scaleFactor, scaleFactor); // scale the context to increase resolution
                  ctx.drawImage(img, 0, 0, img.width, img.height, 0, 0, img.width, img.height);

                  const pngUrl = canvas.toDataURL('image/png');

                  const a = document.createElement('a');
                  a.href = pngUrl;
                  a.download = document.title + '.png';
                  a.click();
                };
              }

            });
            </script>

            <body onload="WaveDrom.ProcessAll()" style="background-color: white;">
              <div style="display: flex; align-items: center; justify-content: flex-end; gap: 15px; margin-top: 10px; margin-bottom: 10px;">
                <div id="svaBtn" style="display: flex; align-items: center; cursor: pointer; background-color: #0e639c; color: white; padding: 8px 12px; border-radius: 4px; border: none; font-size: 14px; transition: background-color 0.2s;">
                  <span style="font-size: 14px; margin-right: 5px;">⚡</span>
                  <span style="font-weight: 600;">Generate SVA</span>
                </div>
                <div id="copyBtn" style="display: flex; align-items: center; cursor: pointer; background-color: #6c757d; color: white; padding: 8px 12px; border-radius: 4px; transition: background-color 0.2s;">
                  <span style="font-size: 14px; margin-right: 5px;">📋</span>
                  <span style="font-weight: 600;">Copy to clipboard</span>
                </div>
              </div>

              <div>
                <script type="WaveDrom">
                  ${waveformJson}
                </script>
              </div>

              <script>
                document.getElementById('copyBtn').addEventListener('click', async () => {
                  const svgEl = document.querySelector('svg');
                  if (!svgEl) {
                    alert('SVG not found!');
                    return;
                  }

                  const svg = new XMLSerializer().serializeToString(svgEl);
                  const svg64 = btoa(unescape(encodeURIComponent(svg)));
                  const img = new Image();
                  img.src = 'data:image/svg+xml;base64,' + svg64;

                  img.onload = async function () {
                    const scaleFactor = 2; // 2x resolution
                    const canvas = document.createElement('canvas');
                    const width = img.width * scaleFactor;
                    const height = img.height * scaleFactor;

                    canvas.width = width;
                    canvas.height = height;
                    const ctx = canvas.getContext('2d');
                    ctx.scale(scaleFactor, scaleFactor); // scale the context to increase resolution
                    ctx.drawImage(img, 0, 0, img.width, img.height, 0, 0, img.width, img.height);

                    const pngUrl = canvas.toDataURL('image/png');
                    const blob = await (await fetch(pngUrl)).blob();

                    try {
                      await navigator.clipboard.write([
                        new ClipboardItem({ [blob.type]: blob })
                      ]);
                      alert('Image copied to clipboard!');
                    } catch (err) {
                      alert('Clipboard copy failed: ' + err.message);
                    }
                  };
                });

                // SVA Generate button click handler
                document.getElementById('svaBtn').addEventListener('click', () => {
                  vscode.postMessage({
                    command: 'generateSVA'
                  });
                });

                // Add hover effects
                document.getElementById('svaBtn').addEventListener('mouseenter', (e) => {
                  e.target.style.backgroundColor = '#1177bb';
                });
                document.getElementById('svaBtn').addEventListener('mouseleave', (e) => {
                  e.target.style.backgroundColor = '#0e639c';
                });

                document.getElementById('copyBtn').addEventListener('mouseenter', (e) => {
                  e.target.style.backgroundColor = '#5a6268';
                });
                document.getElementById('copyBtn').addEventListener('mouseleave', (e) => {
                  e.target.style.backgroundColor = '#6c757d';
                });
              </script>

            </body>
            </html>`;
  }
}

/**
 * Manages SVA Generator webview panel
 */
class SVAGeneratorPanel {
  /**
   * Track the currently panel. Only allow a single panel to exist at a time.
   */
  public static currentPanel: SVAGeneratorPanel | undefined;

  public static readonly viewType = "svaGenerator";

  private readonly _panel: vscode.WebviewPanel;
  private readonly _extensionPath: string;
  private _disposables: vscode.Disposable[] = [];

  public static createOrShow(extensionPath: string) {
    const activeEditor = vscode.window.activeTextEditor;

    // Ensure we have an active editor and it's a JSON file
    if (
      !activeEditor ||
      !(
        activeEditor.document.fileName.toLowerCase().endsWith(".json") ||
        activeEditor.document.fileName.toLowerCase().endsWith(".json5")
      )
    ) {
      vscode.window.showWarningMessage("Please open a JSON file to generate SystemVerilog assertions.");
      return;
    }

    // If we already have a panel
    if (SVAGeneratorPanel.currentPanel) {
      SVAGeneratorPanel.currentPanel._panel.reveal(vscode.ViewColumn.Beside);
      SVAGeneratorPanel.currentPanel._updateWithFileContent();
      return;
    }

    // Otherwise, create a new panel.
    const panel = vscode.window.createWebviewPanel(
      SVAGeneratorPanel.viewType,
      "SystemVerilog Assertions: " + getFilename(),
      { preserveFocus: true, viewColumn: vscode.ViewColumn.Beside },
      {
        enableScripts: true,
        localResourceRoots: [
          vscode.Uri.file(path.join(extensionPath, "localScripts")),
        ],
      }
    );

    SVAGeneratorPanel.currentPanel = new SVAGeneratorPanel(panel, extensionPath);
  }

  private constructor(panel: vscode.WebviewPanel, extensionPath: string) {
    this._panel = panel;
    this._extensionPath = extensionPath;

    this._updateWithFileContent();

    // Listen for when the panel is disposed
    this._panel.onDidDispose(() => this.dispose(), null, this._disposables);

    // Handle messages from the webview
    this._panel.webview.onDidReceiveMessage(
      (message) => {
        switch (message.command) {
          case 'saveSVA':
            this._saveSVAFile(message.content);
            break;
        }
      },
      null,
      this._disposables
    );
  }

  public dispose() {
    SVAGeneratorPanel.currentPanel = undefined;

    // Clean up our resources
    this._panel.dispose();

    while (this._disposables.length) {
      const x = this._disposables.pop();
      if (x) {
        x.dispose();
      }
    }
  }

  private _updateWithFileContent() {
    // Get the current text editor
    const editor = vscode.window.activeTextEditor;
    if (!editor) {
      return;
    }
    
    const doc = editor.document;
    const docContent = doc.getText();

    try {
      // Validate and clean JSON content
      const cleanedContent = this._cleanJsonContent(docContent);
      const jsonData = JSON.parse(cleanedContent);
      const svaCode = this._generateSVAFromJSON(jsonData);
      this._updateWebview(svaCode, getFilename());
    } catch (error) {
      const detailedError = this._analyzeJsonError(docContent, error);
      vscode.window.showErrorMessage(`Failed to parse JSON: ${detailedError}`);
      
      // Show diagnostic information in webview
      const errorReport = this._generateErrorReport(docContent, error);
      this._updateWebview(errorReport, `${getFilename()} - JSON Error`);
    }
  }

  private _generateSVAFromJSON(jsonData: any): string {
    // Convert WaveDrom JSON to SystemVerilog Assertions
    let svaCode = `// SystemVerilog Assertions generated from WaveDrom JSON\n`;
    svaCode += `// Generated on ${new Date().toISOString()}\n`;
    svaCode += `// Based on industry best practices and expert recommendations\n\n`;
    
    if (!jsonData.signal || !Array.isArray(jsonData.signal)) {
      return svaCode + "// Error: No valid signal data found in JSON\n";
    }

    // Extract extended configuration if available (NEW)
    const config = this._parseExtendedConfig(jsonData);
    const clockSignal = config.clock_signal || 'clk';
    const resetSignal = config.reset_signal || 'rst_n';
    const moduleName = config.module_name || 'assertion_module';
    const timeoutCycles = config.timeout_cycles || 10;
    
    // Signal normalization and validation with deduplication
    const { validSignals, warnings } = this._normalizeAndValidateSignals(jsonData.signal);
    const clockInfo = validSignals.find((s: any) => this._isClockSignal(s));
    
    // Add configuration info to output
    if (config.has_extended_config) {
      svaCode += `// Extended Configuration Detected:\n`;
      svaCode += `// - Clock: ${clockSignal}, Reset: ${resetSignal}\n`;
      svaCode += `// - Module: ${moduleName}\n`;
      svaCode += `// - Timeout Cycles: ${timeoutCycles}\n`;
      if (config.prohibition_patterns?.length > 0) {
        svaCode += `// - Prohibition Patterns: ${config.prohibition_patterns.length} configured\n`;
      }
      svaCode += `\n`;
    }
    
    // Add warnings to output
    if (warnings.length > 0) {
      svaCode += `// WARNINGS:\n`;
      warnings.forEach(warning => {
        svaCode += `// - ${warning}\n`;
      });
      svaCode += `\n`;
    }
    
    // Auto-detect protocol patterns and generate optimized assertions
    const protocolAnalysis = this._analyzeProtocolPatterns(validSignals);
    
    svaCode += `// Protocol Analysis: ${protocolAnalysis.detectedProtocols.join(', ')}\n`;
    svaCode += `// Optimization: ${protocolAnalysis.optimizations.join(', ')}\n\n`;
    
    svaCode += `module ${moduleName} (\n`;
    svaCode += `  input logic        ${clockSignal},\n`;
    svaCode += `  input logic        ${resetSignal}`;
    
    // Add all non-clock signals as inputs with proper width detection
    validSignals.forEach((signal: any) => {
      if (!this._isClockSignal(signal)) {
        const signalName = signal.normalizedName;
        const width = this._detectSignalWidth(signal);
        const widthDecl = width > 1 ? `[${width-1}:0] ` : '       ';
        svaCode += `,\n  input logic ${widthDecl} ${signalName}`;
      }
    });
    
    svaCode += `\n);\n\n`;
    
    // Generate efficient, non-redundant assertions based on protocol analysis
    svaCode += this._generateOptimizedAssertions(protocolAnalysis, clockSignal, timeoutCycles);

    svaCode += `endmodule\n`;
    
    return svaCode;
  }

  private _parseExtendedConfig(jsonData: any): any {
    const assertionConfig = jsonData.assertion_config || {};
    const hasExtended = Object.keys(assertionConfig).length > 0;
    
    return {
      has_extended_config: hasExtended,
      clock_signal: assertionConfig.clock_signal || 'clk',
      reset_signal: assertionConfig.reset_signal || 'rst_n',
      module_name: assertionConfig.module_name || 'assertion_module',
      timeout_cycles: assertionConfig.timeout_cycles || 10,
      assertion_strength: assertionConfig.assertion_strength || {},
      prohibition_patterns: assertionConfig.prohibition_patterns || [],
      fixed_latency: assertionConfig.fixed_latency || [],
      signal_change_rules: assertionConfig.signal_change_rules || [],
      generation_options: assertionConfig.generation_options || {}
    };
  }

  private _analyzeProtocolPatterns(signals: any[]): any {
    const protocols: any = {
      detectedProtocols: [],
      optimizations: [],
      signalGroups: {},
      dataSignals: [],
      controlSignals: [],
      clockSignals: [],
      allSignals: signals  // Add reference to all signals
    };
    
    // Group signals by type
    signals.forEach(signal => {
      const name = signal.normalizedName;
      
      if (this._isClockSignal(signal)) {
        protocols.clockSignals.push(signal);
      } else if (name.includes('data') || name.includes('addr')) {
        protocols.dataSignals.push(signal);
      } else {
        protocols.controlSignals.push(signal);
      }
    });
    
    // Detect protocol patterns
    const hasRequest = signals.some(s => s.normalizedName.includes('request') || s.normalizedName.includes('req'));
    const hasAck = signals.some(s => s.normalizedName.includes('acknowledge') || s.normalizedName.includes('ack'));
    const hasValid = signals.some(s => s.normalizedName.includes('valid'));
    const hasReady = signals.some(s => s.normalizedName.includes('ready'));
    
    if (hasRequest && hasAck) {
      protocols.detectedProtocols.push('Request-Acknowledge');
      protocols.signalGroups.reqAck = {
        request: signals.find(s => s.normalizedName.includes('request') || s.normalizedName.includes('req')),
        acknowledge: signals.find(s => s.normalizedName.includes('acknowledge') || s.normalizedName.includes('ack')),
        data: protocols.dataSignals
      };
    }
    
    if (hasValid && hasReady) {
      protocols.detectedProtocols.push('Valid-Ready');
      protocols.signalGroups.validReady = {
        valid: signals.find(s => s.normalizedName.includes('valid')),
        ready: signals.find(s => s.normalizedName.includes('ready')),
        data: protocols.dataSignals
      };
    }
    
    // Determine optimizations
    if (protocols.dataSignals.length === 1) {
      protocols.optimizations.push('Single data signal - unified data assertions');
    }
    
    if (protocols.detectedProtocols.length > 1) {
      protocols.optimizations.push('Multi-protocol - shared data stability checks');
    }
    
    return protocols;
  }

  private _generateOptimizedAssertions(protocolAnalysis: any, clockSignal: string, timeoutCycles: number): string {
    let assertions = `  // === OPTIMIZED ASSERTION GENERATION ===\n\n`;
    
    const { signalGroups, dataSignals, optimizations, allSignals } = protocolAnalysis;
    
    // Generate unified data assertions first (avoid duplication)
    if (dataSignals.length > 0) {
      assertions += this._generateUnifiedDataAssertions(dataSignals, clockSignal);
    }
    
    // Generate protocol-specific assertions
    if (signalGroups.reqAck) {
      assertions += this._generateEfficientRequestAckProtocol(signalGroups.reqAck, clockSignal, timeoutCycles);
    }
    
    if (signalGroups.validReady) {
      assertions += this._generateEfficientValidReadyProtocol(signalGroups.validReady, clockSignal);
    }
    
    // Generate prohibition pattern assertions (NEW)
    assertions += this._generateProhibitionPatterns(allSignals, clockSignal);
    
    // Generate signal change detection assertions (NEW)
    assertions += this._generateSignalChangeAssertions(allSignals, clockSignal);
    
    // Generate fixed latency assertions (NEW)
    assertions += this._generateFixedLatencyAssertions(allSignals, clockSignal);
    
    // Add optimization notes
    if (optimizations.length > 0) {
      assertions += `\n  // Applied optimizations: ${optimizations.join(', ')}\n`;
    }
    
    return assertions;
  }

  private _generateUnifiedDataAssertions(dataSignals: any[], clockSignal: string): string {
    let assertions = `  // === UNIFIED DATA INTEGRITY ASSERTIONS ===\n`;
    
    dataSignals.forEach(dataSignal => {
      const dataName = dataSignal.normalizedName;
      
      // Single comprehensive data assertion
      assertions += `  property ${dataName}_integrity_p;\n`;
      assertions += `    disable iff (!rst_n)\n`;
      assertions += `    @(posedge ${clockSignal}) (${dataName} !== 'x);\n`;
      assertions += `  endproperty\n`;
      assertions += `  ${dataName}_integrity_a: assert property(${dataName}_integrity_p);\n\n`;
    });
    
    return assertions;
  }

  private _generateEfficientRequestAckProtocol(group: any, clockSignal: string, timeoutCycles: number): string {
    const reqName = group.request.normalizedName;
    const ackName = group.acknowledge.normalizedName;
    let assertions = `  // === REQUEST-ACKNOWLEDGE PROTOCOL (OPTIMIZED) ===\n`;
    
    // Core handshake assertion
    assertions += `  property ${reqName}_${ackName}_handshake_p;\n`;
    assertions += `    disable iff (!rst_n)\n`;
    assertions += `    @(posedge ${clockSignal}) $rose(${reqName}) |-> ##[1:${timeoutCycles}] (${ackName} == 1'b1);\n`;
    assertions += `  endproperty\n`;
    assertions += `  ${reqName}_${ackName}_handshake_a: assert property(${reqName}_${ackName}_handshake_p);\n\n`;
    
    // Acknowledge precedence check
    assertions += `  property ${ackName}_has_precedent_${reqName}_p;\n`;
    assertions += `    disable iff (!rst_n)\n`;
    assertions += `    @(posedge ${clockSignal}) $rose(${ackName}) |-> ($past(${reqName}, 1) || $past(${reqName}, 2) || $past(${reqName}, 3));\n`;
    assertions += `  endproperty\n`;
    assertions += `  ${ackName}_has_precedent_${reqName}_a: assert property(${ackName}_has_precedent_${reqName}_p);\n\n`;
    
    // Data stability during transaction (if data exists)
    if (group.data && group.data.length > 0) {
      group.data.forEach((dataSignal: any) => {
        const dataName = dataSignal.normalizedName;
        assertions += `  property ${dataName}_stable_during_${reqName}_${ackName}_p;\n`;
        assertions += `    disable iff (!rst_n)\n`;
        assertions += `    @(posedge ${clockSignal}) $rose(${reqName}) |=> $stable(${dataName}) throughout (${reqName} ##1 ${ackName});\n`;
        assertions += `  endproperty\n`;
        assertions += `  ${dataName}_stable_during_${reqName}_${ackName}_a: assert property(${dataName}_stable_during_${reqName}_${ackName}_p);\n\n`;
      });
    }
    
    return assertions;
  }

  private _generateEfficientValidReadyProtocol(group: any, clockSignal: string): string {
    const validName = group.valid.normalizedName;
    const readyName = group.ready.normalizedName;
    let assertions = `  // === VALID-READY PROTOCOL (OPTIMIZED) ===\n`;
    
    // Valid stability until ready
    assertions += `  property ${validName}_${readyName}_stability_p;\n`;
    assertions += `    disable iff (!rst_n)\n`;
    assertions += `    @(posedge ${clockSignal}) (${validName} == 1'b1) && (${readyName} == 1'b0) |-> ##1 (${validName} == 1'b1);\n`;
    assertions += `  endproperty\n`;
    assertions += `  ${validName}_${readyName}_stability_a: assert property(${validName}_${readyName}_stability_p);\n\n`;
    
    // Ready deassertion rule
    assertions += `  property ${readyName}_deassert_rule_p;\n`;
    assertions += `    disable iff (!rst_n)\n`;
    assertions += `    @(posedge ${clockSignal}) $fell(${readyName}) |-> (${validName} == 1'b0);\n`;
    assertions += `  endproperty\n`;
    assertions += `  ${readyName}_deassert_rule_a: assert property(${readyName}_deassert_rule_p);\n\n`;
    
    return assertions;
  }

  private _generateProhibitionPatterns(signals: any[], clockSignal: string): string {
    let assertions = `  // === PROHIBITION PATTERN ASSERTIONS ===\n`;
    
    // Look for potential prohibition patterns
    const fullSignals = signals.filter(s => s.normalizedName.includes('full'));
    const writeSignals = signals.filter(s => s.normalizedName.includes('write') || s.normalizedName.includes('wen'));
    const emptySignals = signals.filter(s => s.normalizedName.includes('empty'));
    const readSignals = signals.filter(s => s.normalizedName.includes('read') || s.normalizedName.includes('ren'));
    const busySignals = signals.filter(s => s.normalizedName.includes('busy'));
    const enableSignals = signals.filter(s => s.normalizedName.includes('enable') || s.normalizedName.includes('en'));
    
    // FIFO overflow prevention
    fullSignals.forEach(fullSignal => {
      writeSignals.forEach(writeSignal => {
        const fullName = fullSignal.normalizedName;
        const writeName = writeSignal.normalizedName;
        
        assertions += `  property no_${fullName}_${writeName}_p;\n`;
        assertions += `    disable iff (!rst_n)\n`;
        assertions += `    @(posedge ${clockSignal}) not (${fullName} && ${writeName});\n`;
        assertions += `  endproperty\n`;
        assertions += `  no_${fullName}_${writeName}_a: assert property(no_${fullName}_${writeName}_p)\n`;
        assertions += `    else $error("FIFO overflow: write attempted when full");\n\n`;
      });
    });
    
    // FIFO underflow prevention
    emptySignals.forEach(emptySignal => {
      readSignals.forEach(readSignal => {
        const emptyName = emptySignal.normalizedName;
        const readName = readSignal.normalizedName;
        
        assertions += `  property no_${emptyName}_${readName}_p;\n`;
        assertions += `    disable iff (!rst_n)\n`;
        assertions += `    @(posedge ${clockSignal}) not (${emptyName} && ${readName});\n`;
        assertions += `  endproperty\n`;
        assertions += `  no_${emptyName}_${readName}_a: assert property(no_${emptyName}_${readName}_p)\n`;
        assertions += `    else $error("FIFO underflow: read attempted when empty");\n\n`;
      });
    });
    
    // Busy signal conflicts
    busySignals.forEach(busySignal => {
      enableSignals.forEach(enableSignal => {
        const busyName = busySignal.normalizedName;
        const enableName = enableSignal.normalizedName;
        
        assertions += `  property no_${busyName}_${enableName}_p;\n`;
        assertions += `    disable iff (!rst_n)\n`;
        assertions += `    @(posedge ${clockSignal}) not (${busyName} && ${enableName});\n`;
        assertions += `  endproperty\n`;
        assertions += `  no_${busyName}_${enableName}_a: assert property(no_${busyName}_${enableName}_p)\n`;
        assertions += `    else $error("Operation attempted while busy");\n\n`;
      });
    });
    
    if (assertions === `  // === PROHIBITION PATTERN ASSERTIONS ===\n`) {
      assertions += `  // No prohibition patterns detected\n\n`;
    }
    
    return assertions;
  }

  private _generateSignalChangeAssertions(signals: any[], clockSignal: string): string {
    let assertions = `  // === SIGNAL CHANGE DETECTION ASSERTIONS ===\n`;
    
    const enableSignals = signals.filter(s => 
      s.normalizedName.includes('enable') || 
      s.normalizedName.includes('en') ||
      s.normalizedName.includes('trigger')
    );
    const outputSignals = signals.filter(s => 
      s.normalizedName.includes('out') || 
      s.normalizedName.includes('output') ||
      s.normalizedName.includes('result')
    );
    
    // Generate enable -> output change assertions
    enableSignals.forEach(enableSignal => {
      outputSignals.forEach(outputSignal => {
        const enableName = enableSignal.normalizedName;
        const outputName = outputSignal.normalizedName;
        
        if (enableName !== outputName) {
          assertions += `  property ${enableName}_causes_${outputName}_change_p;\n`;
          assertions += `    disable iff (!rst_n)\n`;
          assertions += `    @(posedge ${clockSignal}) $rose(${enableName}) |-> $changed(${outputName});\n`;
          assertions += `  endproperty\n`;
          assertions += `  ${enableName}_causes_${outputName}_change_a: assert property(${enableName}_causes_${outputName}_change_p)\n`;
          assertions += `    else $error("${outputName} did not change when ${enableName} asserted");\n\n`;
        }
      });
    });
    
    // Generate edge detection for control signals
    const controlSignals = signals.filter(s => 
      !this._isClockSignal(s) && 
      !s.normalizedName.includes('data') && 
      !s.normalizedName.includes('addr')
    );
    
    controlSignals.forEach(signal => {
      const signalName = signal.normalizedName;
      
      // Generate $rose() and $fell() monitoring
      assertions += `  // Edge monitoring for ${signalName}\n`;
      assertions += `  property ${signalName}_edge_stability_p;\n`;
      assertions += `    disable iff (!rst_n)\n`;
      assertions += `    @(posedge ${clockSignal}) $rose(${signalName}) |-> ##1 ${signalName};\n`;
      assertions += `  endproperty\n`;
      assertions += `  ${signalName}_edge_stability_a: assert property(${signalName}_edge_stability_p)\n`;
      assertions += `    else $error("${signalName} fell immediately after rising");\n\n`;
    });
    
    if (assertions === `  // === SIGNAL CHANGE DETECTION ASSERTIONS ===\n`) {
      assertions += `  // No signal change patterns detected\n\n`;
    }
    
    return assertions;
  }

  private _generateFixedLatencyAssertions(signals: any[], clockSignal: string): string {
    let assertions = `  // === FIXED LATENCY ASSERTIONS ===\n`;
    
    // Analyze wave patterns for fixed latency relationships
    const latencyPatterns = this._detectFixedLatencyPatterns(signals);
    
    latencyPatterns.forEach(pattern => {
      const { trigger, response, type } = pattern;
      
      if (type === 'fixed') {
        const { cycles, confidence } = pattern;
        assertions += `  // Fixed latency detected: ${cycles} cycles (confidence: ${(confidence * 100).toFixed(0)}%)\n`;
        assertions += `  property ${trigger}_to_${response}_fixed_latency_p;\n`;
        assertions += `    disable iff (!rst_n)\n`;
        assertions += `    @(posedge ${clockSignal}) $rose(${trigger}) |-> ##${cycles} $rose(${response});\n`;
        assertions += `  endproperty\n`;
        assertions += `  ${trigger}_to_${response}_fixed_latency_a: assert property(${trigger}_to_${response}_fixed_latency_p)\n`;
        assertions += `    else $error("${response} did not respond exactly ${cycles} cycles after ${trigger}");\n\n`;
      } else if (type === 'variable') {
        const { minCycles, maxCycles, confidence } = pattern;
        assertions += `  // Variable latency detected: ${minCycles}-${maxCycles} cycles (confidence: ${(confidence * 100).toFixed(0)}%)\n`;
        assertions += `  property ${trigger}_to_${response}_variable_latency_p;\n`;
        assertions += `    disable iff (!rst_n)\n`;
        assertions += `    @(posedge ${clockSignal}) $rose(${trigger}) |-> ##[${minCycles}:${maxCycles}] $rose(${response});\n`;
        assertions += `  endproperty\n`;
        assertions += `  ${trigger}_to_${response}_variable_latency_a: assert property(${trigger}_to_${response}_variable_latency_p)\n`;
        assertions += `    else $error("${response} did not respond within ${minCycles}-${maxCycles} cycles after ${trigger}");\n\n`;
      }
    });
    
    if (assertions === `  // === FIXED LATENCY ASSERTIONS ===\n`) {
      assertions += `  // No timing patterns detected from waveform analysis\n\n`;
    }
    
    return assertions;
  }

  private _detectFixedLatencyPatterns(signals: any[]): any[] {
    const patterns: any[] = [];
    
    // Identify potential trigger and response signals
    const triggerSignals = signals.filter(s => 
      s.normalizedName.includes('request') || 
      s.normalizedName.includes('start') ||
      s.normalizedName.includes('trigger') ||
      s.normalizedName.includes('issue')
    );
    
    const responseSignals = signals.filter(s => 
      s.normalizedName.includes('acknowledge') || 
      s.normalizedName.includes('done') ||
      s.normalizedName.includes('complete') ||
      s.normalizedName.includes('commit')
    );
    
    triggerSignals.forEach(trigger => {
      responseSignals.forEach(response => {
        if (trigger.normalizedName !== response.normalizedName) {
          // Analyze actual wave patterns to detect timing
          const detectedLatency = this._analyzeWaveformTiming(trigger, response);
          
          if (detectedLatency.isFixed) {
            patterns.push({
              trigger: trigger.normalizedName,
              response: response.normalizedName,
              cycles: detectedLatency.cycles,
              confidence: detectedLatency.confidence,
              type: 'fixed'
            });
          } else if (detectedLatency.hasPattern) {
            // Variable latency detected
            patterns.push({
              trigger: trigger.normalizedName,
              response: response.normalizedName,
              minCycles: detectedLatency.minCycles,
              maxCycles: detectedLatency.maxCycles,
              confidence: detectedLatency.confidence,
              type: 'variable'
            });
          }
        }
      });
    });
    
    return patterns;
  }

  private _analyzeWaveformTiming(triggerSignal: any, responseSignal: any): any {
    const triggerWave = triggerSignal.wave;
    const responseWave = responseSignal.wave;
    
    if (!triggerWave || !responseWave) {
      return { isFixed: false, hasPattern: false, confidence: 0 };
    }
    
    // Find rising edges in both signals
    const triggerEdges = this._findRisingEdges(triggerWave);
    const responseEdges = this._findRisingEdges(responseWave);
    
    if (triggerEdges.length === 0 || responseEdges.length === 0) {
      return { isFixed: false, hasPattern: false, confidence: 0 };
    }
    
    // Calculate latencies between trigger and response
    const latencies: number[] = [];
    
    triggerEdges.forEach(triggerPos => {
      // Find the next response edge after this trigger
      const nextResponseEdge = responseEdges.find(respPos => respPos > triggerPos);
      if (nextResponseEdge !== undefined) {
        latencies.push(nextResponseEdge - triggerPos);
      }
    });
    
    if (latencies.length === 0) {
      return { isFixed: false, hasPattern: false, confidence: 0 };
    }
    
    // Check if all latencies are the same (fixed latency)
    const uniqueLatencies = [...new Set(latencies)];
    
    if (uniqueLatencies.length === 1) {
      return {
        isFixed: true,
        cycles: uniqueLatencies[0],
        confidence: 0.9,
        hasPattern: true
      };
    } else {
      // Variable latency
      return {
        isFixed: false,
        hasPattern: true,
        minCycles: Math.min(...latencies),
        maxCycles: Math.max(...latencies),
        confidence: 0.7
      };
    }
  }

  private _findRisingEdges(wave: string): number[] {
    const edges: number[] = [];
    
    for (let i = 1; i < wave.length; i++) {
      const prev = wave[i - 1];
      const curr = wave[i];
      
      // Rising edge: 0->1, l->1, l->h, 0->h, etc.
      if ((prev === '0' || prev === 'l') && (curr === '1' || curr === 'h')) {
        edges.push(i);
      }
      // Also consider transitions from '.' (continue previous) where previous was low
      else if (prev === '0' && curr === '.') {
        // Look ahead to see if this becomes a rising edge
        let j = i;
        while (j < wave.length && wave[j] === '.') j++;
        if (j < wave.length && (wave[j] === '1' || wave[j] === 'h')) {
          edges.push(j);
        }
      }
    }
    
    return edges;
  }

  private _cleanJsonContent(content: string): string {
    // Remove comments (// style and /* */ style)
    let cleaned = content.replace(/\/\/.*$/gm, '');
    cleaned = cleaned.replace(/\/\*[\s\S]*?\*\//g, '');
    
    // Remove trailing commas before ] or }
    cleaned = cleaned.replace(/,(\s*[\]}])/g, '$1');
    
    // Remove multiple spaces and normalize whitespace
    cleaned = cleaned.replace(/\s+/g, ' ').trim();
    
    return cleaned;
  }

  private _analyzeJsonError(content: string, error: any): string {
    const message = error.message || 'Unknown JSON error';
    
    // Try to extract position information
    const positionMatch = message.match(/position (\d+)/i);
    if (positionMatch) {
      const position = parseInt(positionMatch[1]);
      const before = content.substring(Math.max(0, position - 20), position);
      const after = content.substring(position, Math.min(content.length, position + 20));
      return `${message}\nNear: "${before}[HERE]${after}"`;
    }
    
    // Look for common JSON issues
    if (message.includes('Unexpected token')) {
      const tokenMatch = message.match(/Unexpected token (.+?) in/i);
      if (tokenMatch) {
        const token = tokenMatch[1];
        return `${message}\nHint: Check for missing commas, extra commas, or unquoted strings around "${token}"`;
      }
    }
    
    // Check for trailing comma issues
    if (content.includes(',]') || content.includes(',}')) {
      return `${message}\nHint: Remove trailing commas before ] or }`;
    }
    
    return message;
  }

  private _generateErrorReport(content: string, error: any): string {
    const lines = content.split('\n');
    let report = `// JSON Parsing Error Report\n`;
    report += `// Error: ${error.message}\n`;
    report += `// Generated: ${new Date().toISOString()}\n\n`;
    
    report += `/*\nCommon JSON Issues and Solutions:\n\n`;
    report += `1. Trailing Commas:\n`;
    report += `   ❌ Bad:   { "name": "test", }\n`;
    report += `   ✅ Good:  { "name": "test" }\n\n`;
    
    report += `2. Missing Commas:\n`;
    report += `   ❌ Bad:   { "a": 1 "b": 2 }\n`;
    report += `   ✅ Good:  { "a": 1, "b": 2 }\n\n`;
    
    report += `3. Unquoted Keys:\n`;
    report += `   ❌ Bad:   { name: "test" }\n`;
    report += `   ✅ Good:  { "name": "test" }\n\n`;
    
    report += `4. Comments (not allowed in strict JSON):\n`;
    report += `   ❌ Bad:   { "name": "test" // comment }\n`;
    report += `   ✅ Good:  { "name": "test" }\n\n`;
    
    // Analyze the specific content
    report += `Analysis of your JSON:\n`;
    
    // Check for trailing commas
    const trailingCommas = [];
    lines.forEach((line, index) => {
      if (line.match(/,\s*[\]}]/)) {
        trailingCommas.push(`Line ${index + 1}: ${line.trim()}`);
      }
    });
    
    if (trailingCommas.length > 0) {
      report += `\n🔍 Found trailing commas:\n`;
      trailingCommas.forEach(issue => report += `   ${issue}\n`);
    }
    
    // Check for missing commas
    const missingCommas = [];
    lines.forEach((line, index) => {
      if (line.match(/[^,]\s*$/) && index < lines.length - 1) {
        const nextLine = lines[index + 1].trim();
        if (nextLine.match(/^["'\w]/) && !line.match(/[\[{]\s*$/)) {
          missingCommas.push(`Line ${index + 1}: ${line.trim()}`);
        }
      }
    });
    
    if (missingCommas.length > 0) {
      report += `\n🔍 Possible missing commas:\n`;
      missingCommas.forEach(issue => report += `   ${issue}\n`);
    }
    
    report += `\n*/\n`;
    
    return report;
  }

  private _normalizeAndValidateSignals(signals: any[]): { validSignals: any[], warnings: string[] } {
    const validSignals: any[] = [];
    const warnings: string[] = [];
    const seenNames = new Set<string>();
    
    signals.forEach((signal, index) => {
      // Skip empty objects or objects without required properties
      if (!signal || typeof signal !== 'object' || !signal.name || !signal.wave) {
        if (signal && Object.keys(signal).length > 0) {
          warnings.push(`Skipping invalid signal at index ${index}: missing name or wave property`);
        }
        return;
      }
      
      // Normalize signal name
      const originalName = signal.name;
      const normalizedName = originalName.replace(/[^a-zA-Z0-9_]/g, '_').toLowerCase();
      
      // Check for duplicates
      if (seenNames.has(normalizedName)) {
        warnings.push(`Duplicate signal name detected: "${originalName}" -> "${normalizedName}"`);
        return;
      }
      seenNames.add(normalizedName);
      
      // Check data width
      const width = this._detectSignalWidth(signal);
      if (width === 8 && !signal.width && (normalizedName.includes('data') || normalizedName.includes('addr'))) {
        warnings.push(`Data width not specified for "${originalName}", defaulting to 8 bits`);
      }
      
      // Create normalized signal object
      validSignals.push({
        ...signal,
        originalName: originalName,
        normalizedName: normalizedName,
        detectedWidth: width
      });
    });
    
    return { validSignals, warnings };
  }

  private _isClockSignal(signal: any): boolean {
    const name = signal.name.toLowerCase();
    const wave = signal.wave;
    return name.includes('clk') || name.includes('clock') || wave.includes('p') || wave.includes('P');
  }

  private _generateRequestAckProtocol(reqSignal: any, ackSignal: any, dataSignal: any, clockSignal: string, timeoutCycles: number): string {
    const reqName = reqSignal.normalizedName;
    const ackName = ackSignal.normalizedName;
    let assertions = `  // Request-Acknowledge Protocol (Improved with Expert Recommendations)\n`;
    
    // Request gets acknowledge within timeout
    assertions += `  property ${reqName}_gets_${ackName}_p;\n`;
    assertions += `    disable iff (!rst_n)\n`;
    assertions += `    @(posedge ${clockSignal}) $rose(${reqName}) |-> ##[1:${timeoutCycles}] (${ackName} == 1'b1);\n`;
    assertions += `  endproperty\n`;
    assertions += `  ${reqName}_gets_${ackName}_a: assert property(${reqName}_gets_${ackName}_p);\n\n`;
    
    // Acknowledge follows request
    assertions += `  property ${ackName}_follows_${reqName}_p;\n`;
    assertions += `    disable iff (!rst_n)\n`;
    assertions += `    @(posedge ${clockSignal}) $rose(${ackName}) |-> ($past(${reqName}, 1) || $past(${reqName}, 2) || $past(${reqName}, 3));\n`;
    assertions += `  endproperty\n`;
    assertions += `  ${ackName}_follows_${reqName}_a: assert property(${ackName}_follows_${reqName}_p);\n\n`;
    
    // Data stability during transaction (if data signal exists)
    if (dataSignal) {
      const dataName = dataSignal.normalizedName;
      
      // Data stable from request to acknowledge
      assertions += `  property ${dataName}_stable_during_transaction_p;\n`;
      assertions += `    disable iff (!rst_n)\n`;
      assertions += `    @(posedge ${clockSignal}) $rose(${reqName}) |=> $stable(${dataName}) throughout (${reqName} ##1 ${ackName});\n`;
      assertions += `  endproperty\n`;
      assertions += `  ${dataName}_stable_during_transaction_a: assert property(${dataName}_stable_during_transaction_p);\n\n`;
      
      // Data should not be X when request is active (limited to active period)
      assertions += `  property ${dataName}_no_x_when_active_p;\n`;
      assertions += `    disable iff (!rst_n)\n`;
      assertions += `    @(posedge ${clockSignal}) (${reqName} == 1'b1) |-> (${dataName} !== 'x);\n`;
      assertions += `  endproperty\n`;
      assertions += `  ${dataName}_no_x_when_active_a: assert property(${dataName}_no_x_when_active_p);\n\n`;
    }
    
    return assertions;
  }

  private _generateValidReadyProtocol(validSignal: any, readySignal: any, dataSignal: any, clockSignal: string): string {
    const validName = validSignal.normalizedName;
    const readyName = readySignal.normalizedName;
    let assertions = `  // Valid-Ready Handshake Protocol (Improved with Expert Recommendations)\n`;
    
    // Valid must remain stable until ready
    assertions += `  property ${validName}_stable_until_ready_p;\n`;
    assertions += `    disable iff (!rst_n)\n`;
    assertions += `    @(posedge ${clockSignal}) (${validName} == 1'b1) && (${readyName} == 1'b0) |-> ##1 (${validName} == 1'b1);\n`;
    assertions += `  endproperty\n`;
    assertions += `  ${validName}_stable_until_ready_a: assert property(${validName}_stable_until_ready_p);\n\n`;
    
    // Ready can only deassert when valid is low
    assertions += `  property ${readyName}_deassert_when_not_valid_p;\n`;
    assertions += `    disable iff (!rst_n)\n`;
    assertions += `    @(posedge ${clockSignal}) $fell(${readyName}) |-> (${validName} == 1'b0);\n`;
    assertions += `  endproperty\n`;
    assertions += `  ${readyName}_deassert_when_not_valid_a: assert property(${readyName}_deassert_when_not_valid_p);\n\n`;
    
    // Data stability during valid-ready handshake
    if (dataSignal) {
      const dataName = dataSignal.normalizedName;
      
      assertions += `  property ${dataName}_stable_during_valid_p;\n`;
      assertions += `    disable iff (!rst_n)\n`;
      assertions += `    @(posedge ${clockSignal}) $rose(${validName}) |=> $stable(${dataName}) throughout (${validName} ##1 (${validName} && ${readyName}));\n`;
      assertions += `  endproperty\n`;
      assertions += `  ${dataName}_stable_during_valid_a: assert property(${dataName}_stable_during_valid_p);\n\n`;
      
      // X check limited to active period
      assertions += `  property ${dataName}_no_x_when_valid_p;\n`;
      assertions += `    disable iff (!rst_n)\n`;
      assertions += `    @(posedge ${clockSignal}) (${validName} == 1'b1) |-> (${dataName} !== 'x);\n`;
      assertions += `  endproperty\n`;
      assertions += `  ${dataName}_no_x_when_valid_a: assert property(${dataName}_no_x_when_valid_p);\n\n`;
    }
    
    return assertions;
  }

  private _generateDataIntegrityAssertions(dataSignal: any, clockSignal: string): string {
    const dataName = dataSignal.normalizedName;
    let assertions = `  // Data Integrity Assertions (Expert Recommended - Conservative)\n`;
    
    // Basic data integrity - simplified and conservative
    assertions += `  property ${dataName}_no_x_basic_p;\n`;
    assertions += `    disable iff (!rst_n)\n`;
    assertions += `    @(posedge ${clockSignal}) (${dataName} !== 'x);\n`;
    assertions += `  endproperty\n`;
    assertions += `  ${dataName}_no_x_basic_a: assert property(${dataName}_no_x_basic_p);\n\n`;
    
    return assertions;
  }

  private _detectSignalWidth(signal: any): number {
    // Explicit width declaration
    if (signal.width) return signal.width;
    
    // Detect from signal name
    const name = signal.name.toLowerCase();
    if (name.includes('data') || name.includes('addr')) {
      return 8; // Common data/address width
    }
    
    // Detect from wave pattern
    const wave = signal.wave;
    if (wave.includes('x') || wave.includes('=') || signal.data) {
      return 8; // Data signals typically 8-bit
    }
    
    // Check for multi-bit patterns (2-9, a-f)
    if (/[2-9a-fA-F]/.test(wave)) {
      return 4; // 4-bit for hex patterns
    }
    
    // Default to single bit for control signals
    return 1;
  }

  private _generateClockAssertion(signalName: string, wave: string): string {
    const clockName = signalName.toLowerCase();
    let assertion = `  // Clock Signal Assertions (Improved)\n`;
    assertion += `  property ${clockName}_clock_period_p;\n`;
    assertion += `    disable iff (!rst_n)\n`;
    assertion += `    @(posedge ${clockName}) ##1 (${clockName} == 1'b0) ##1 (${clockName} == 1'b1);\n`;
    assertion += `  endproperty\n`;
    assertion += `  ${clockName}_clock_period_a: assert property(${clockName}_clock_period_p);\n\n`;
    return assertion;
  }

  private _updateWebview(svaContent: string, filename: string) {
    this._panel.webview.html = this._getHtmlForWebview(svaContent, filename);
  }

  private _getHtmlForWebview(svaContent: string, filename: string): string {
    return `<!DOCTYPE html>
            <html lang="en">
            <head>
                <meta charset="UTF-8">
                <meta name="viewport" content="width=device-width, initial-scale=1.0">
                <title>SystemVerilog Assertions: ${filename}</title>
                <style>
                    body {
                        font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
                        margin: 20px;
                        background-color: #1e1e1e;
                        color: #d4d4d4;
                    }
                    .header {
                        background-color: #2d2d2d;
                        padding: 15px;
                        border-radius: 5px;
                        margin-bottom: 20px;
                    }
                    .code-container {
                        background-color: #252526;
                        border: 1px solid #3e3e3e;
                        border-radius: 5px;
                        padding: 20px;
                        overflow-x: auto;
                    }
                    .code {
                        white-space: pre;
                        font-size: 14px;
                        line-height: 1.5;
                    }
                    .save-button {
                        background-color: #0e639c;
                        color: white;
                        border: none;
                        padding: 10px 20px;
                        border-radius: 3px;
                        cursor: pointer;
                        font-size: 14px;
                        margin-top: 15px;
                    }
                    .save-button:hover {
                        background-color: #1177bb;
                    }
                    .keyword {
                        color: #569cd6;
                    }
                    .comment {
                        color: #6a9955;
                    }
                    .string {
                        color: #ce9178;
                    }
                </style>
            </head>
            <body>
                <div class="header">
                    <h2>SystemVerilog Assertions Generator</h2>
                    <p>Generated from: ${filename}.json</p>
                    <button class="save-button" onclick="saveSVA()">💾 Save as .sv file</button>
                </div>
                
                <div class="code-container">
                    <div class="code">${this._highlightSyntax(svaContent)}</div>
                </div>

                <script>
                    const vscode = acquireVsCodeApi();
                    
                    function saveSVA() {
                        const content = ${JSON.stringify(svaContent)};
                        vscode.postMessage({
                            command: 'saveSVA',
                            content: content
                        });
                    }
                </script>
            </body>
            </html>`;
  }

  private _highlightSyntax(code: string): string {
    // Basic syntax highlighting for SystemVerilog
    return code
      .replace(/\/\/.*$/gm, '<span class="comment">$&</span>')
      .replace(/\b(module|endmodule|property|endproperty|assert|assume|cover|clk|posedge|negedge)\b/g, '<span class="keyword">$1</span>')
      .replace(/"[^"]*"/g, '<span class="string">$&</span>');
  }

  private async _saveSVAFile(content: string) {
    const activeEditor = vscode.window.activeTextEditor;
    if (!activeEditor) {
      return;
    }

    const originalUri = activeEditor.document.uri;
    const originalPath = originalUri.fsPath;
    const baseName = path.basename(originalPath, path.extname(originalPath));
    const dirName = path.dirname(originalPath);
    const svaPath = path.join(dirName, `${baseName}_assertions.sv`);
    const reportPath = path.join(dirName, `${baseName}_report.md`);

    try {
      // Save SVA file
      const svaUri = vscode.Uri.file(svaPath);
      const writeData = new TextEncoder().encode(content);
      await vscode.workspace.fs.writeFile(svaUri, writeData);
      
      // Generate and save report
      const report = this._generateReport(content);
      const reportUri = vscode.Uri.file(reportPath);
      const reportData = new TextEncoder().encode(report);
      await vscode.workspace.fs.writeFile(reportUri, reportData);
      
      vscode.window.showInformationMessage(`SystemVerilog assertions saved to: ${baseName}_assertions.sv\nReport saved to: ${baseName}_report.md`);
      
      // Optionally open the generated file
      const doc = await vscode.workspace.openTextDocument(svaUri);
      await vscode.window.showTextDocument(doc);
    } catch (error) {
      vscode.window.showErrorMessage(`Failed to save SVA file: ${error.message}`);
    }
  }

  private _generateReport(svaContent: string): string {
    const timestamp = new Date().toISOString();
    return `# SystemVerilog Assertions Generation Report

Generated: ${timestamp}

## Review Checklist

Please review the following items before using the generated assertions:

### ✅ **Mandatory Checks**
- [ ] Verify signal names match your design
- [ ] Confirm data bit widths are correct
- [ ] Validate timeout values (##[1:10]) match your timing requirements
- [ ] Check that reset signal (rst_n) is available in your design
- [ ] Review protocol assumptions (Request-Ack vs Valid-Ready)

### ⚠️ **Configuration Items**
- [ ] Adjust max_ack_delay if different from [1:10] cycles
- [ ] Modify data_width if defaulted to 8 bits
- [ ] Customize clock signal name if not 'clk'
- [ ] Add additional protocol-specific assertions if needed

### 🔧 **Integration Notes**
- All assertions use \`disable iff (!rst_n)\` for reset handling
- Signal names are normalized to lowercase with underscores
- X-checks are limited to active transaction periods
- Conservative timeout ranges are used by default

### 📋 **Next Steps**
1. Include this .sv file in your testbench
2. Connect signals according to the module interface
3. Run initial simulations to verify assertion behavior
4. Tune timing parameters based on actual design specs
5. Add design-specific assertions as needed

---
*This report was automatically generated by WaveRender SVA Extension*
`;
  }
}
