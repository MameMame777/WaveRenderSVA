import * as path from "path";
import * as vscode from 'vscode';

// NodeInfo interface for WaveDrom node analysis
interface NodeInfo {
  id: string;           // 'a', 'b', 'c'...
  signalName: string;   // 'req', 'ack', 'data'...
  position: number;     // タイミング位置
  eventType: string;    // 'rising_edge', 'falling_edge', 'data_change', 'stable'
}

// EdgeInfo interface for WaveDrom edge analysis
interface EdgeInfo {
  sourceNode: string;   // Source node ID
  targetNode: string;   // Target node ID
  edgeType: string;     // 'sharp_line', 'spline'
  operator: string;     // '-|>', '<->', '~', etc.
  label?: string;       // Optional label
  description?: string; // Pattern description for debugging/documentation
}

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
  private _currentConfig: any = null;

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
    // Generate SystemVerilog Assertions from WaveDrom edge/node/comment syntax
    return this._generateSVAFromWaveDrom(jsonData);
  }

  private _generateSVAFromWaveDrom(jsonData: any): string {
    let svaCode = `// SystemVerilog Assertions generated from WaveDrom edge/node/comment syntax\n`;
    svaCode += `// Generated on ${new Date().toISOString()}\n`;
    svaCode += `// Using WaveDrom Sharp Lines and Splines for timing relationships\n\n`;
    
    // Basic JSON validation
    if (!jsonData.signal || !Array.isArray(jsonData.signal)) {
      return svaCode + "// Error: No valid signal data found in JSON\n";
    }

    try {
      // Phase 1: Parse nodes from signal definitions
      const nodeMap = this._parseNodes(jsonData.signal);
      
      // Phase 2: Parse edges if they exist
      const edges = jsonData.edge ? this._parseEdges(jsonData.edge) : [];
      
      // Phase 3: Extract comments for additional assertion hints
      const comments = this._extractComments(jsonData);
      
      // Phase 4: Generate SystemVerilog module
      svaCode += this._generateSystemVerilogModule(nodeMap, edges, comments);
      
    } catch (error) {
      svaCode += `// Error during WaveDrom processing: ${error}\n`;
    }

    return svaCode;
  }

  // Phase 2: Node analysis methods
  private _parseNodes(signals: any[]): Map<string, NodeInfo> {
    const nodeMap = new Map<string, NodeInfo>();
    
    signals.forEach(signal => {
      if (!signal.node || !signal.name) return;
      
      const nodeString = signal.node as string;
      const signalName = signal.name as string;
      const waveString = signal.wave as string;
      
      // Parse each position in the node string to find node IDs
      for (let position = 0; position < nodeString.length; position++) {
        const nodeChar = nodeString[position];
        
        // Skip dots and spaces (no nodes at these positions)
        if (nodeChar === '.' || nodeChar === ' ') continue;
        
        // Extract node ID (a, b, c, etc.)
        const nodeId = nodeChar;
        
        // Determine event type from wave transition at this position
        const eventType = this._detectEventType(waveString, position);
        
        // Create node info
        const nodeInfo: NodeInfo = {
          id: nodeId,
          signalName: signalName,
          position: position,
          eventType: eventType
        };
        
        nodeMap.set(nodeId, nodeInfo);
      }
    });
    
    return nodeMap;
  }

  // Helper method to detect event type from wave transition
  private _detectEventType(waveString: string, position: number): string {
    if (!waveString || position >= waveString.length) {
      return 'unknown';
    }
    
    const currentChar = waveString[position];
    const prevChar = position > 0 ? waveString[position - 1] : '';
    
    // Detect rising edge (0 -> 1)
    if (prevChar === '0' && currentChar === '1') {
      return 'rising_edge';
    }
    
    // Detect falling edge (1 -> 0)
    if (prevChar === '1' && currentChar === '0') {
      return 'falling_edge';
    }
    
    // Detect data change (any transition that's not rising/falling edge)
    if (prevChar && prevChar !== currentChar && 
        !((prevChar === '0' && currentChar === '1') || (prevChar === '1' && currentChar === '0'))) {
      return 'data_change';
    }
    
    // Detect stable state (same as previous)
    if (prevChar === currentChar) {
      return 'stable';
    }
    
    // Default for initial state or unknown transitions
    return 'initial_state';
  }

  // Phase 3: Edge analysis methods
  private _parseEdges(edges: string[]): EdgeInfo[] {
    const parsedEdges: EdgeInfo[] = [];
    
    edges.forEach(edgeString => {
      const edgeInfo = this._parseEdgeString(edgeString);
      if (edgeInfo) {
        parsedEdges.push(edgeInfo);
      }
    });
    
    return parsedEdges;
  }

  // Parse individual edge string with comprehensive Sharp Lines and Splines support
  private _parseEdgeString(edgeString: string): EdgeInfo | null {
    if (!edgeString || typeof edgeString !== 'string') {
      return null;
    }

    // Remove label if present (everything after space)
    const parts = edgeString.trim().split(' ');
    const edgePart = parts[0];
    const label = parts.length > 1 ? parts.slice(1).join(' ') : undefined;

    // Sharp Lines patterns (strict timing constraints)
    const sharpLinePatterns = [
      { pattern: /<->/, operator: '<->', type: 'bidirectional_sharp', description: 'Strict bidirectional relationship' },
      { pattern: /<-\|-/, operator: '<-|-', type: 'reverse_sharp_end', description: 'Reverse strict endpoint' },
      { pattern: /-\|\->/, operator: '-|->', type: 'sharp_line_arrow', description: 'Strict delay relationship' },
      { pattern: /-\|>/, operator: '-|>', type: 'sharp_line_simple', description: 'Short strict delay' },
      { pattern: /\|->/, operator: '|->', type: 'conditional_sharp', description: 'Conditional strict relationship' },
      { pattern: /-\|-/, operator: '-|-', type: 'one_cycle_delay', description: '1 cycle delay' },
      { pattern: /->/, operator: '->', type: 'strict_direction', description: 'Strict direction' },
      { pattern: /-\|/, operator: '-|', type: 'immediate_causality', description: 'Immediate causality' },
      { pattern: /-/, operator: '-', type: 'basic_connection', description: 'Basic connection' },
      { pattern: /\+/, operator: '+', type: 'logical_and', description: 'Logical AND relationship' }
    ];

    // Splines patterns (flexible timing constraints)
    const splinePatterns = [
      { pattern: /<-~>/, operator: '<-~>', type: 'wide_bidirectional_spline', description: 'Wide bidirectional' },
      { pattern: /<~>/, operator: '<~>', type: 'bidirectional_spline', description: 'Flexible bidirectional relationship' },
      { pattern: /<~-/, operator: '<~-', type: 'reverse_spline', description: 'Reverse flexible' },
      { pattern: /-~>/, operator: '-~>', type: 'flexible_delay', description: 'Flexible delay relationship' },
      { pattern: /~->/, operator: '~->', type: 'flexible_direction', description: 'Flexible direction' },
      { pattern: /-~/, operator: '-~', type: 'flexible_relation', description: 'Flexible relationship' },
      { pattern: /~/, operator: '~', type: 'flexible_connection', description: 'Flexible connection' }
    ];

    // Try to match sharp line patterns first
    for (const { pattern, operator, type, description } of sharpLinePatterns) {
      const match = edgePart.match(new RegExp(`(.+)${pattern.source}(.+)`));
      if (match) {
        return {
          sourceNode: match[1],
          targetNode: match[2],
          edgeType: 'sharp_line',
          operator: operator,
          label: label,
          description: description
        };
      }
    }

    // Try to match spline patterns
    for (const { pattern, operator, type, description } of splinePatterns) {
      const match = edgePart.match(new RegExp(`(.+)${pattern.source}(.+)`));
      if (match) {
        return {
          sourceNode: match[1],
          targetNode: match[2],
          edgeType: 'spline',
          operator: operator,
          label: label,
          description: description
        };
      }
    }

    // If no pattern matches, try simple node-to-node connection
    if (edgePart.length >= 2) {
      return {
        sourceNode: edgePart[0],
        targetNode: edgePart[edgePart.length - 1],
        edgeType: 'simple',
        operator: 'simple',
        label: label
      };
    }

    return null;
  }

  // Extract comments from JSON for assertion hints
  private _extractComments(jsonData: any): string[] {
    const comments: string[] = [];
    
    // Look for head/foot text that might contain assertion hints
    if (jsonData.head && jsonData.head.text) {
      comments.push(`head: ${jsonData.head.text}`);
    }
    
    if (jsonData.foot && jsonData.foot.text) {
      comments.push(`foot: ${jsonData.foot.text}`);
    }
    
    // Look for signal-level comments in data arrays
    if (jsonData.signal) {
      jsonData.signal.forEach((signal: any, index: number) => {
        if (signal.data && Array.isArray(signal.data)) {
          signal.data.forEach((dataItem: any, dataIndex: number) => {
            if (typeof dataItem === 'string' && dataItem.includes('//')) {
              comments.push(`signal[${index}].data[${dataIndex}]: ${dataItem}`);
            }
          });
        }
      });
    }
    
    // Look for edge labels that might contain assertion hints
    if (jsonData.edge) {
      jsonData.edge.forEach((edge: any, index: number) => {
        if (typeof edge === 'string' && edge.includes(' ')) {
          const parts = edge.split(' ');
          if (parts.length > 1) {
            const label = parts.slice(1).join(' ');
            comments.push(`edge[${index}]: ${label}`);
          }
        }
      });
    }
    
    return comments;
  }

  // Generate SystemVerilog module from nodes, edges, and comments
  private _generateSystemVerilogModule(nodeMap: Map<string, NodeInfo>, edges: EdgeInfo[], comments?: string[]): string {
    // Module structure generation
    const moduleInfo = this._analyzeModuleRequirements(nodeMap, edges);
    
    let moduleCode = `// ========================================\n`;
    moduleCode += `// WaveDrom-generated SystemVerilog Assertions\n`;
    moduleCode += `// Generated: ${new Date().toISOString()}\n`;
    moduleCode += `// Sharp Lines: Strict timing constraints\n`;
    moduleCode += `// Splines: Flexible timing constraints\n`;
    if (comments && comments.length > 0) {
      moduleCode += `// Comments: ${comments.join(', ')}\n`;
    }
    moduleCode += `// ========================================\n\n`;
    
    // Module declaration
    moduleCode += `module ${moduleInfo.moduleName} (\n`;
    moduleCode += `  input logic ${moduleInfo.clockSignal},\n`;
    moduleCode += `  input logic ${moduleInfo.resetSignal}`;
    
    // Signal declarations
    moduleInfo.signals.forEach(signal => {
      if (signal.name !== moduleInfo.clockSignal && signal.name !== moduleInfo.resetSignal) {
        moduleCode += `,\n  ${signal.direction} ${signal.type} ${signal.name}`;
      }
    });
    
    moduleCode += `\n);\n\n`;
    
    // Generate properties and assertions
    moduleCode += this._generateEdgeBasedProperties(nodeMap, edges, comments);
    
    moduleCode += `endmodule\n`;
    
    return moduleCode;
  }

  // Generate edge-based properties and assertions
  private _generateEdgeBasedProperties(nodeMap: Map<string, NodeInfo>, edges: EdgeInfo[], comments?: string[]): string {
    let propertyCode = `  // ========================================\n`;
    propertyCode += `  // Edge-based Property Definitions\n`;
    propertyCode += `  // ========================================\n\n`;
    
    // Generate properties from edges
    edges.forEach((edge, index) => {
      const sourceNode = nodeMap.get(edge.sourceNode);
      const targetNode = nodeMap.get(edge.targetNode);
      
      if (sourceNode && targetNode) {
        const propertyName = `edge_${edge.sourceNode}_to_${edge.targetNode}_${index}`;
        const propertyBody = this._generatePropertyBody(sourceNode, targetNode, edge);
        
        propertyCode += `  // ${edge.description || edge.label || 'Timing relationship'}\n`;
        propertyCode += `  property ${propertyName};\n`;
        propertyCode += `    @(posedge clk) disable iff (!rst_n)\n`;
        propertyCode += `    ${propertyBody};\n`;
        propertyCode += `  endproperty\n`;
        propertyCode += `  ${propertyName}_a: assert property(${propertyName})\n`;
        propertyCode += `    else $error("[SVA] Edge timing violation: %s -> %s at time %0t (operator: ${edge.operator})", "${edge.sourceNode}", "${edge.targetNode}", $time);\n\n`;
      }
    });
    
    // Generate properties from comments if they contain timing hints
    if (comments && comments.length > 0) {
      propertyCode += `  // Comment-derived properties\n`;
      comments.forEach((comment, index) => {
        const timing = this._extractTimingFromComment(comment);
        if (timing) {
          propertyCode += `  // From comment: ${comment}\n`;
          propertyCode += `  property comment_timing_${index};\n`;
          propertyCode += `    @(posedge clk) disable iff (!rst_n)\n`;
          propertyCode += `    ${timing};\n`;
          propertyCode += `  endproperty\n`;
          propertyCode += `  comment_timing_${index}_a: assert property(comment_timing_${index});\n\n`;
        }
      });
    }
    
    // If no edges found, generate basic node-based assertions
    if (edges.length === 0) {
      propertyCode += `  // No edges found - generating basic node assertions\n`;
      nodeMap.forEach((node, nodeId) => {
        const event = this._getSystemVerilogEvent(node);
        propertyCode += `  // Node ${nodeId} assertion\n`;
        propertyCode += `  property node_${nodeId}_event;\n`;
        propertyCode += `    @(posedge clk) disable iff (!rst_n)\n`;
        propertyCode += `    ${event} |-> 1'b1;\n`;
        propertyCode += `  endproperty\n`;
        propertyCode += `  node_${nodeId}_a: assert property(node_${nodeId}_event);\n\n`;
      });
    }
    
    return propertyCode;
  }

  // Extract timing constraints from comments
  private _extractTimingFromComment(comment: string): string | null {
    // Look for timing patterns in comments like "t1", "2 cycles", "within 5ms" etc.
    const timingPatterns = [
      { pattern: /(\w+)\s+within\s+(\d+)\s*cycles?/i, format: '$1 |-> ##[1:$2] 1\'b1' },
      { pattern: /(\w+)\s+after\s+(\d+)\s*cycles?/i, format: '$1 |-> ##$2 1\'b1' },
      { pattern: /t(\d+)/i, format: '1\'b1 |-> ##$1 1\'b1' },
      { pattern: /delay\s+(\d+)/i, format: '1\'b1 |-> ##$1 1\'b1' },
      { pattern: /(\d+)\s*ms/i, format: '1\'b1 |-> ##[$1*1000:$1*2000] 1\'b1' }
    ];
    
    for (const { pattern, format } of timingPatterns) {
      const match = comment.match(pattern);
      if (match) {
        return format.replace(/\$(\d+)/g, (_, num) => match[parseInt(num)] || '1');
      }
    }
    
    return null;
  }

  // Analyze module requirements from nodes and edges
  private _analyzeModuleRequirements(nodeMap: Map<string, NodeInfo>, edges: EdgeInfo[]): any {
    const signals = new Map<string, any>();
    
    // Extract signal information from nodes
    nodeMap.forEach(node => {
      if (!signals.has(node.signalName)) {
        signals.set(node.signalName, {
          name: node.signalName,
          direction: 'input',
          type: 'logic',
          width: '[0:0]' // Default width, could be enhanced to detect actual width
        });
      }
    });
    
    return {
      moduleName: 'wavedrom_assertions',
      clockSignal: 'clk',
      resetSignal: 'rst_n',
      signals: Array.from(signals.values())
    };
  }

  // Generate property body based on edge type and timing
  private _generatePropertyBody(sourceNode: NodeInfo, targetNode: NodeInfo, edge: EdgeInfo): string {
    const sourceEvent = this._getSystemVerilogEvent(sourceNode);
    const targetEvent = this._getSystemVerilogEvent(targetNode);
    const timingDiff = targetNode.position - sourceNode.position;
    
    // Generate assertion based on edge type and operator
    if (edge.edgeType === 'sharp_line') {
      return this._generateSharpLinePropertyBody(sourceEvent, targetEvent, edge.operator, timingDiff);
    } else if (edge.edgeType === 'spline') {
      return this._generateSplinePropertyBody(sourceEvent, targetEvent, edge.operator, timingDiff);
    } else {
      const timingClause = timingDiff > 0 ? `##${timingDiff}` : '';
      return `${sourceEvent} |-> ${timingClause} ${targetEvent}`;
    }
  }

  // Sharp Lines property body generation - LRM準拠版
  private _generateSharpLinePropertyBody(sourceEvent: string, targetEvent: string, operator: string, timingDiff: number): string {
    switch (operator) {
      case '<->':  return `(${sourceEvent} == ${targetEvent})`; // 同値関係（双方向ではない）
      case '-|->': return `${sourceEvent} |=> ##${Math.max(timingDiff, 1)} ${targetEvent}`;
      case '-|>':  return `${sourceEvent} |=> ${targetEvent}`;
      case '|->':  return `${sourceEvent} |-> ${timingDiff > 0 ? `##${timingDiff}` : ''} ${targetEvent}`;
      case '-|-':  return `${sourceEvent} |=> ##1 ${targetEvent}`;
      case '->':   return `${sourceEvent} |=> ${timingDiff > 0 ? `##${timingDiff}` : ''} ${targetEvent}`;
      case '-|':   return `${sourceEvent} |=> ${targetEvent}`;
      case '+':    return `(${sourceEvent} && ${targetEvent})`;
      case '-':    return `${sourceEvent} |=> ${timingDiff > 0 ? `##${timingDiff}` : ''} ${targetEvent}`;
      default:     return `${sourceEvent} |-> ${timingDiff > 0 ? `##${timingDiff}` : ''} ${targetEvent}`;
    }
  }

  // Splines property body generation - LRM準拠版
  private _generateSplinePropertyBody(sourceEvent: string, targetEvent: string, operator: string, timingDiff: number): string {
    switch (operator) {
      case '<-~>': return `${sourceEvent} |=> ##[0:${Math.max(timingDiff + 2, 3)}] ${targetEvent}`;
      case '<~>':  return `${sourceEvent} |-> ##[0:$] ${targetEvent}`; // weak eventually
      case '-~>':  return `${sourceEvent} |=> ##[1:${Math.max(timingDiff, 1) + 2}] ${targetEvent}`;
      case '~->':  return `${sourceEvent} |-> ##[0:$] ${targetEvent}`; // weak eventually
      case '-~':   return `${sourceEvent} |=> ##[0:${Math.max(timingDiff + 1, 2)}] ${targetEvent}`;
      case '~-':   return `${sourceEvent} |=> ##[0:${Math.max(timingDiff + 1, 2)}] ${targetEvent}`;
      case '~>':   return `${sourceEvent} |-> ##[0:$] ${targetEvent}`; // weak eventually
      case '~':    return `${sourceEvent} |=> ##[0:$] ${targetEvent}`; // strong eventually
      default:     return `${sourceEvent} |-> ##[0:$] ${targetEvent}`;
    }
  }

  // Convert node event type to SystemVerilog event expression
  private _getSystemVerilogEvent(node: NodeInfo): string {
    switch (node.eventType) {
      case 'rising_edge':
        return `$rose(${node.signalName})`;
      case 'falling_edge':
        return `$fell(${node.signalName})`;
      case 'data_change':
        return `$changed(${node.signalName})`;
      case 'stable':
        return `$stable(${node.signalName})`;
      default:
        return node.signalName; // Simple signal reference
    }
  }

  private _parseExtendedConfig(jsonData: any): any {
    const assertionConfig = jsonData.assertion_config || {};
    const hasExtended = Object.keys(assertionConfig).length > 0;
    
    // Parse protocol definitions
    const protocols = jsonData.protocols || {};
    
    // Parse timing relationships
    const timingRelationships = jsonData.timing_relationships || [];
    
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
      generation_options: assertionConfig.generation_options || {},
      
      // Extended features
      protocols: protocols,
      timing_relationships: timingRelationships,
      custom_properties: assertionConfig.custom_properties || [],
      has_protocol_definitions: Object.keys(protocols).length > 0,
      has_timing_definitions: timingRelationships.length > 0
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
      allSignals: signals,  // Add reference to all signals
      explicitProtocols: {}  // For JSON-defined protocols
    };
    
    // Group signals by type (enhanced with explicit types)
    signals.forEach(signal => {
      const name = signal.normalizedName || signal.name;
      const signalType = signal.type || 'unknown';
      
      if (this._isClockSignal(signal) || signalType === 'clock') {
        protocols.clockSignals.push(signal);
      } else if (this._isDataSignal(signal) || signalType === 'data') {
        protocols.dataSignals.push(signal);
      } else {
        protocols.controlSignals.push(signal);
      }
      
      // Group by explicit protocol assignment
      if (signal.protocol) {
        if (!protocols.explicitProtocols[signal.protocol]) {
          protocols.explicitProtocols[signal.protocol] = [];
        }
        protocols.explicitProtocols[signal.protocol].push(signal);
      }
    });
    
    // Detect protocol patterns (enhanced with explicit definitions)
    const hasRequest = signals.some(s => s.normalizedName?.includes('request') || s.normalizedName?.includes('req') || s.role === 'handshake_initiator');
    const hasAck = signals.some(s => s.normalizedName?.includes('acknowledge') || s.normalizedName?.includes('ack') || s.role === 'handshake_response');
    const hasValid = signals.some(s => s.normalizedName?.includes('valid') || s.role === 'data_qualifier');
    const hasReady = signals.some(s => s.normalizedName?.includes('ready') || s.role === 'flow_control');
    
    if (hasRequest && hasAck) {
      protocols.detectedProtocols.push('Request-Acknowledge');
      protocols.signalGroups.reqAck = {
        request: signals.find(s => s.normalizedName?.includes('request') || s.normalizedName?.includes('req') || s.role === 'handshake_initiator'),
        acknowledge: signals.find(s => s.normalizedName?.includes('acknowledge') || s.normalizedName?.includes('ack') || s.role === 'handshake_response'),
        data: protocols.dataSignals
      };
    }
    
    if (hasValid && hasReady) {
      protocols.detectedProtocols.push('Valid-Ready');
      protocols.signalGroups.validReady = {
        valid: signals.find(s => s.normalizedName?.includes('valid') || s.role === 'data_qualifier'),
        ready: signals.find(s => s.normalizedName?.includes('ready') || s.role === 'flow_control'),
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
    
    // Add explicit protocol optimizations
    if (Object.keys(protocols.explicitProtocols).length > 0) {
      protocols.optimizations.push('Explicit protocol definitions - enhanced accuracy');
    }
    
    return protocols;
  }

  private _generateOptimizedAssertions(protocolAnalysis: any, clockSignal: string, timeoutCycles: number, config?: any): string {
    // Store config for use in other methods
    this._currentConfig = config;
    
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
    assertions += this._generateProhibitionPatterns(allSignals, clockSignal, config);
    
    // Generate signal change detection assertions (NEW)
    assertions += this._generateSignalChangeAssertions(allSignals, clockSignal, config);
    
    // Generate reset behavior assertions (ADVICE2 REQUIREMENT)
    assertions += this._generateResetBehaviorAssertions(allSignals, clockSignal, config);
    
    // Generate variable latency assertions (ADVICE2 REQUIREMENT)
    assertions += this._generateVariableLatencyAssertions(allSignals, clockSignal, config);
    
    // Generate sequential protocol assertions (ADVICE2 REQUIREMENT)
    assertions += this._generateSequentialProtocolAssertions(allSignals, clockSignal, config);
    
    // Generate fixed latency assertions (NEW)
    assertions += this._generateFixedLatencyAssertions(allSignals, clockSignal);
    
    // Generate custom properties from JSON config (NEW)
    assertions += this._generateCustomProperties(clockSignal);
    
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

  private _generateProhibitionPatterns(signals: any[], clockSignal: string, config: any): string {
    let assertions = `  // === PROHIBITION PATTERN ASSERTIONS (ADVICE2) ===\n`;
    
    // Check for explicit conflict signals from extended config
    const extendedConfig = config?.extended_config;
    if (extendedConfig?.conflict_signals) {
      extendedConfig.conflict_signals.forEach((conflict: any) => {
        const signal1 = conflict.signal1;
        const signal2 = conflict.signal2;
        const description = conflict.description || `${signal1} and ${signal2} conflict`;
        
        assertions += `  // ${description}\n`;
        assertions += `  property no_${signal1}_${signal2}_conflict_p;\n`;
        assertions += `    disable iff (!rst_n)\n`;
        assertions += `    @(posedge ${clockSignal}) not (${signal1} && ${signal2});\n`;
        assertions += `  endproperty\n`;
        assertions += `  no_${signal1}_${signal2}_conflict_a: assert property(no_${signal1}_${signal2}_conflict_p)\n`;
        assertions += `    else $error("${description}");\n\n`;
      });
    }
    
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

  private _generateSignalChangeAssertions(signals: any[], clockSignal: string, config: any): string {
    let assertions = `  // === SIGNAL CHANGE DETECTION ASSERTIONS (ADVICE2) ===\n`;
    
    // Check for explicit edge detection from extended config
    const extendedConfig = config?.extended_config;
    if (extendedConfig?.edge_detection) {
      extendedConfig.edge_detection.forEach((edge: any) => {
        const trigger = edge.trigger;
        const target = edge.target;
        const type = edge.type || 'change';
        const description = edge.description || `${trigger} -> ${target} ${type}`;
        
        assertions += `  // ${description}\n`;
        assertions += `  property ${trigger}_${target}_${type}_p;\n`;
        assertions += `    disable iff (!rst_n)\n`;
        
        if (type === 'change') {
          assertions += `    @(posedge ${clockSignal}) ${trigger} |-> $changed(${target});\n`;
        } else if (type === 'rose') {
          assertions += `    @(posedge ${clockSignal}) ${trigger} |-> $rose(${target});\n`;
        } else if (type === 'fell') {
          assertions += `    @(posedge ${clockSignal}) ${trigger} |-> $fell(${target});\n`;
        }
        
        assertions += `  endproperty\n`;
        assertions += `  ${trigger}_${target}_${type}_a: assert property(${trigger}_${target}_${type}_p)\n`;
        assertions += `    else $error("${target} did not ${type} when ${trigger}=1");\n\n`;
      });
    }
    
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

  private _generateCustomProperties(clockSignal: string): string {
    let assertions = `  // === CUSTOM PROPERTIES ===\n`;
    
    // Get custom properties from JSON config
    const config = this._getCurrentConfig();
    if (config && config.custom_properties && config.custom_properties.length > 0) {
      config.custom_properties.forEach((prop: any) => {
        const propName = prop.name;
        const description = prop.description || 'Custom property';
        const trigger = prop.trigger || 'always';
        const condition = prop.condition;
        
        assertions += `  // ${description}\n`;
        assertions += `  property ${propName}_p;\n`;
        assertions += `    disable iff (!rst_n)\n`;
        
        if (trigger === 'always') {
          assertions += `    @(posedge ${clockSignal}) ${condition};\n`;
        } else {
          assertions += `    @(posedge ${clockSignal}) ${trigger} |-> ${condition};\n`;
        }
        
        assertions += `  endproperty\n`;
        assertions += `  ${propName}_a: assert property(${propName}_p)\n`;
        assertions += `    else $error("Custom property '${propName}' violated: ${description}");\n\n`;
      });
    } else {
      assertions += `  // No custom properties defined\n\n`;
    }
    
    return assertions;
  }

  private _getCurrentConfig(): any {
    return this._currentConfig;
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

  private _analyzeWaveformDetails(signals: any[]): any {
    const analysis = {
      totalSignals: 0,
      dataSignals: 0,
      controlSignals: 0,
      clockSignals: 0,
      detectedDataWidths: [] as number[],
      signalPatterns: {} as { [key: string]: any }
    };
    
    signals.forEach((signal, index) => {
      if (!signal.wave || signal.wave === '' || !signal.name) {
        return; // Skip empty or spacer signals
      }
      
      analysis.totalSignals++;
      const signalName = signal.name;
      const wavePattern = signal.wave;
      const dataArray = signal.data || [];
      
      // Classify signal type
      if (this._isClockSignal(signal)) {
        analysis.clockSignals++;
      } else if (this._isDataSignal(signal)) {
        analysis.dataSignals++;
        const width = this._detectSignalWidth(signal);
        if (!analysis.detectedDataWidths.includes(width)) {
          analysis.detectedDataWidths.push(width);
        }
      } else {
        analysis.controlSignals++;
      }
      
      // Detailed pattern analysis
      analysis.signalPatterns[signalName] = this._analyzeIndividualWavePattern(wavePattern, dataArray);
    });
    
    analysis.detectedDataWidths.sort((a, b) => a - b);
    return analysis;
  }

  private _isDataSignal(signal: any): boolean {
    // Check explicit signal type
    if (signal.type === 'data') {
      return true;
    }
    
    const name = signal.name ? signal.name.toLowerCase() : '';
    const wave = signal.wave || '';
    
    // Check name patterns
    if (name.includes('data') || name.includes('addr') || name.includes('bus')) {
      return true;
    }
    
    // Check wave pattern for data characteristics
    if (wave.includes('=') || signal.data || /[2-9a-fA-F]/.test(wave)) {
      return true;
    }
    
    return false;
  }

  private _detectSignalWidth(signal: any): number {
    // Explicit width declaration (highest priority)
    if (signal.width) return signal.width;
    
    // For single-bit control signals explicitly marked
    if (signal.type === 'control' && signal.width === 1) {
      return 1;
    }
    
    // Analyze data array for actual bit requirements
    if (signal.data && Array.isArray(signal.data)) {
      const maxValue = signal.data.reduce((max, val) => {
        if (typeof val === 'string') {
          // Parse hex, binary, or decimal values
          const numVal = val.startsWith('0x') ? parseInt(val, 16) :
                        val.startsWith('0b') ? parseInt(val, 2) :
                        isNaN(parseInt(val)) ? 0 : parseInt(val);
          return Math.max(max, numVal);
        }
        return Math.max(max, typeof val === 'number' ? val : 0);
      }, 0);
      
      if (maxValue > 0) {
        // Calculate minimum bits needed
        const bitsNeeded = Math.ceil(Math.log2(maxValue + 1));
        // Round up to common widths
        if (bitsNeeded <= 1) return 1;
        if (bitsNeeded <= 4) return 4;
        if (bitsNeeded <= 8) return 8;
        if (bitsNeeded <= 16) return 16;
        if (bitsNeeded <= 32) return 32;
        return 64;
      }
    }
    
    // Analyze wave pattern for data complexity
    const wave = signal.wave;
    if (wave) {
      // Count unique non-control states
      const dataStates = wave.match(/[2-9a-fA-F]/g);
      if (dataStates) {
        const uniqueStates = new Set(dataStates).size;
        if (uniqueStates > 8) return 8;  // More than 8 states likely 8-bit
        if (uniqueStates > 4) return 4;  // More than 4 states likely 4-bit
        if (uniqueStates > 2) return 3;  // More than 2 states likely 3-bit
        return 2;  // Simple data signal
      }
    }
    
    // Detect from signal name with improved heuristics
    const name = signal.name ? signal.name.toLowerCase() : '';
    if (name.includes('addr') || name.includes('address')) {
      return 32; // Address typically 32-bit
    }
    if (name.includes('data') || name.includes('bus')) {
      return 8; // Data bus typically 8-bit
    }
    if (name.includes('count') || name.includes('cnt')) {
      return 8; // Counters typically 8-bit
    }
    if (name.includes('id') || name.includes('tag')) {
      return 4; // IDs typically 4-bit
    }
    
    // Check for multi-bit patterns in wave
    if (wave && /[2-9a-fA-F]/.test(wave)) {
      return 4; // 4-bit for hex patterns
    }
    
    // Default single bit for control signals
    return 1;
  }

  private _analyzeIndividualWavePattern(wavePattern: string, dataArray: string[]): any {
    const analysis = {
      length: wavePattern.length,
      hasUnknownStates: wavePattern.includes('x'),
      hasTristate: wavePattern.includes('z'),
      hasDataTransitions: /[2-9a-fA-F=]/.test(wavePattern),
      transitions: [] as any[],
      stableRegions: [] as any[],
      edgeCount: 0
    };
    
    // Count transitions
    for (let i = 0; i < wavePattern.length - 1; i++) {
      if (wavePattern[i] !== wavePattern[i + 1] && wavePattern[i] !== '.' && wavePattern[i + 1] !== '.') {
        analysis.transitions.push({
          position: i + 1,
          from: wavePattern[i],
          to: wavePattern[i + 1]
        });
        analysis.edgeCount++;
      }
    }
    
    return analysis;
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

  // === ADVICE2.MD REQUIREMENT IMPLEMENTATIONS ===
  
  /**
   * Generate variable latency assertions - ADVICE2 Requirement 1 & 4
   * Supports ##[min:max] patterns like ##[1:3] ack
   */
  private _generateVariableLatencyAssertions(signals: any[], clockSignal: string, config: any): string {
    let assertions = `  // === VARIABLE LATENCY ASSERTIONS (ADVICE2) ===\n`;
    
    // Look for extended config patterns
    const extendedConfig = config?.extended_config;
    if (extendedConfig?.timing_relationships) {
      extendedConfig.timing_relationships.forEach((timing: any) => {
        if (timing.type === 'variable_latency' && timing.min_cycles && timing.max_cycles) {
          const triggerSignal = timing.trigger_signal;
          const responseSignal = timing.response_signal;
          
          assertions += `  // ${triggerSignal} -> ${responseSignal} within ${timing.min_cycles}-${timing.max_cycles} cycles\n`;
          assertions += `  property ${triggerSignal}_to_${responseSignal}_variable_latency_p;\n`;
          assertions += `    disable iff (!rst_n)\n`;
          assertions += `    @(posedge ${clockSignal}) $rose(${triggerSignal}) |-> ##[${timing.min_cycles}:${timing.max_cycles}] ${responseSignal};\n`;
          assertions += `  endproperty\n`;
          assertions += `  ${triggerSignal}_to_${responseSignal}_variable_latency_a: assert property(${triggerSignal}_to_${responseSignal}_variable_latency_p)\n`;
          assertions += `    else $error("${responseSignal.toUpperCase()} not asserted within ${timing.min_cycles}-${timing.max_cycles} cycles after ${triggerSignal.toUpperCase()}");\n\n`;
        }
      });
    }
    
    // Auto-detect common handshake patterns
    const controlSignals = signals.filter(s => 
      s.wave && !s.wave.includes('p') && !s.wave.includes('n') && 
      (s.name.toLowerCase().includes('req') || s.name.toLowerCase().includes('ack') ||
       s.name.toLowerCase().includes('valid') || s.name.toLowerCase().includes('ready'))
    );
    
    if (controlSignals.length >= 2) {
      // Generate typical 1-3 cycle handshake patterns
      const reqSignal = controlSignals.find(s => s.name.toLowerCase().includes('req') || s.name.toLowerCase().includes('valid'));
      const ackSignal = controlSignals.find(s => s.name.toLowerCase().includes('ack') || s.name.toLowerCase().includes('ready'));
      
      if (reqSignal && ackSignal && reqSignal !== ackSignal) {
        const reqName = reqSignal.normalizedName;
        const ackName = ackSignal.normalizedName;
        
        assertions += `  // Auto-detected handshake: ${reqName} -> ${ackName} within 1-3 cycles\n`;
        assertions += `  property ${reqName}_${ackName}_handshake_variable_p;\n`;
        assertions += `    disable iff (!rst_n)\n`;
        assertions += `    @(posedge ${clockSignal}) $rose(${reqName}) |-> ##[1:3] ${ackName};\n`;
        assertions += `  endproperty\n`;
        assertions += `  ${reqName}_${ackName}_handshake_variable_a: assert property(${reqName}_${ackName}_handshake_variable_p)\n`;
        assertions += `    else $error("${ackName.toUpperCase()} not asserted within 1-3 cycles after ${reqName.toUpperCase()}");\n\n`;
      }
    }
    
    if (assertions === `  // === VARIABLE LATENCY ASSERTIONS (ADVICE2) ===\n`) {
      assertions += `  // No variable latency patterns detected\n\n`;
    }
    
    return assertions;
  }

  /**
   * Generate sequential protocol assertions - ADVICE2 Requirement 4
   * Supports A -> B -> C sequence chains
   */
  private _generateSequentialProtocolAssertions(signals: any[], clockSignal: string, config: any): string {
    let assertions = `  // === SEQUENTIAL PROTOCOL ASSERTIONS (ADVICE2) ===\n`;
    
    // Look for extended config sequence chains
    const extendedConfig = config?.extended_config;
    if (extendedConfig?.sequence_chains) {
      extendedConfig.sequence_chains.forEach((sequence: any) => {
        const seqSignals = sequence.signals;
        if (seqSignals && seqSignals.length >= 2) {
          const seqName = sequence.name || seqSignals.join('_');
          
          assertions += `  // Sequential protocol: ${seqSignals.join(' -> ')}\n`;
          assertions += `  property ${seqName}_sequence_p;\n`;
          assertions += `    disable iff (!rst_n)\n`;
          assertions += `    @(posedge ${clockSignal}) $rose(${seqSignals[0]})`;
          
          for (let i = 1; i < seqSignals.length; i++) {
            const delay = sequence.delays?.[i-1] || '[1:5]';
            assertions += ` |-> ##${delay} $rose(${seqSignals[i]})`;
          }
          
          assertions += `;\n  endproperty\n`;
          assertions += `  ${seqName}_sequence_a: assert property(${seqName}_sequence_p)\n`;
          assertions += `    else $error("Protocol sequence violated: ${seqSignals.join(' -> ')}");\n\n`;
        }
      });
    }
    
    // Auto-detect common state machine patterns
    const stateSignals = signals.filter(s => 
      s.wave && (
        s.name.toLowerCase().includes('start') || 
        s.name.toLowerCase().includes('busy') || 
        s.name.toLowerCase().includes('done') || 
        s.name.toLowerCase().includes('valid') ||
        s.name.toLowerCase().includes('ready')
      )
    );
    
    if (stateSignals.length >= 3) {
      const startSignal = stateSignals.find(s => s.name.toLowerCase().includes('start'));
      const busySignal = stateSignals.find(s => s.name.toLowerCase().includes('busy'));
      const doneSignal = stateSignals.find(s => s.name.toLowerCase().includes('done'));
      
      if (startSignal && busySignal && doneSignal) {
        const startName = startSignal.normalizedName;
        const busyName = busySignal.normalizedName;
        const doneName = doneSignal.normalizedName;
        
        assertions += `  // Auto-detected state machine: ${startName} -> ${busyName} -> ${doneName}\n`;
        assertions += `  property state_machine_sequence_p;\n`;
        assertions += `    disable iff (!rst_n)\n`;
        assertions += `    @(posedge ${clockSignal}) $rose(${startName}) |-> ##[1:5] $rose(${busyName}) ##[1:10] $rose(${doneName});\n`;
        assertions += `  endproperty\n`;
        assertions += `  state_machine_sequence_a: assert property(state_machine_sequence_p)\n`;
        assertions += `    else $error("State machine sequence violated: ${startName} -> ${busyName} -> ${doneName}");\n\n`;
      }
    }
    
    if (assertions === `  // === SEQUENTIAL PROTOCOL ASSERTIONS (ADVICE2) ===\n`) {
      assertions += `  // No sequential protocol patterns detected\n\n`;
    }
    
    return assertions;
  }

  /**
   * Generate reset behavior assertions - ADVICE2 Requirement 2
   * Supports reset -> ##1 (!ready && !busy) patterns
   */
  private _generateResetBehaviorAssertions(signals: any[], clockSignal: string, config: any): string {
    let assertions = `  // === RESET BEHAVIOR ASSERTIONS (ADVICE2) ===\n`;
    
    const extendedConfig = config?.extended_config;
    if (extendedConfig?.reset_behavior) {
      const resetBehavior = extendedConfig.reset_behavior;
      const resetSignal = resetBehavior.reset_signal;
      const resetTargets = resetBehavior.reset_targets || [];
      
      if (resetTargets.length > 0) {
        const conditions = resetTargets.map((target: any) => 
          target.value === "0" ? `!${target.signal}` : target.signal
        ).join(' && ');
        
        assertions += `  // ${resetBehavior.description || 'Reset behavior'}\n`;
        assertions += `  property reset_behavior_p;\n`;
        assertions += `    @(posedge ${clockSignal}) ${resetSignal} |-> ##1 (${conditions});\n`;
        assertions += `  endproperty\n`;
        assertions += `  reset_behavior_a: assert property(reset_behavior_p)\n`;
        assertions += `    else $error("Reset did not clear ready/busy correctly");\n\n`;
      }
    }
    
    if (assertions === `  // === RESET BEHAVIOR ASSERTIONS (ADVICE2) ===\n`) {
      assertions += `  // No reset behavior patterns configured\n\n`;
    }
    
    return assertions;
  }
}
