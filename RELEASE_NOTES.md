# Release Notes v0.29.0 - Code Optimization & Performance Enhancement

## 🎯 Major Code Cleanup

### 📉 Code Size Reduction

- **Removed unused functions**: Eliminated 21 deprecated functions (835 lines, 31.6% reduction)
- **Streamlined codebase**: From 2,643 lines to 1,808 lines
- **Improved maintainability**: Cleaner, more focused implementation
- **Better performance**: Reduced memory footprint and faster loading

### 🔧 Architectural Improvements

- **Unified SVA generation**: Consolidated to single `WaveformToSVAGenerator` class
- **Removed legacy code**: Eliminated old WaveDrom direct parsing methods
- **Modern implementation**: Focus on new, efficient generation pipeline
- **Error-free compilation**: All TypeScript compilation issues resolved

### 🗑️ Removed Deprecated Functions

- Old WaveDrom parsing functions (`_parseNodes`, `_detectEventType`, `_parseEdges`)
- Unused signal processing (`_normalizeAndValidateSignals`, `_detectSignalWidth`)
- Legacy assertion generators (`_generateRequestAckProtocol`, `_generateDataIntegrityAssertions`)
- Obsolete analysis functions (`_analyzeWaveformDetails`, `_analyzeIndividualWavePattern`)

## ✅ Quality Assurance

- **Zero compilation errors**: Clean TypeScript build
- **Maintained functionality**: All core features preserved
- **Improved code clarity**: Easier to understand and maintain

---

## Release Notes v0.27.0 - Enhanced SVA Generation & Code Quality

## 🎉 Major Improvements

### ⚡ SystemVerilog Assertion Generation Enhanced
- **Advanced logical operators**: AND (`$&()`), OR (`$|()`), NOT (`$!()`), IMPLIES (`$->()`) support
- **Enhanced timing relationships**: Sharp lines and splines for precise timing constraints
- **Professional assertion patterns**: Clock domain crossing, handshake protocols, data stability
- **Comprehensive edge detection**: Rising, falling, and transition-based assertions

### 🌐 Internationalization
- **All user messages translated to English** for global accessibility
- **Professional error messaging** with clear guidance
- **Consistent terminology** throughout the extension

### 🔧 Code Quality & Reliability
- **ESLint integration**: Migrated from deprecated tslint to modern ESLint v9
- **Error reduction**: 2859 → 10 linting errors (97% improvement)
- **Consistent code formatting**: Tab-based indentation throughout
- **Type safety improvements**: Better TypeScript type definitions

### 📚 Documentation Overhaul
- **Comprehensive README**: Installation, usage, and contribution guidelines
- **Sample files**: Ready-to-use examples in `examples/` directory
- **Command reference**: Complete list of all available commands and keybindings
- **Developer guide**: Setup instructions for contributors

## 🚀 New Features

### WaveDrom Edge Syntax Support
```json
{
  "edge": [
    "a~>b",    // Flexible timing relationship
    "c-|>d",   // Sharp timing constraint
    "e<->f"    // Bidirectional relationship
  ]
}
```

### Enhanced Logical Conditions
```json
{
  "text": [
    "$&(enable && ready)$",     // AND condition
    "$|(reset || error)$",      // OR condition  
    "$!(busy)$",                // NOT condition
    "$->(valid)$"               // IMPLIES condition
  ]
}
```

### Professional SVA Output
```systemverilog
// Enhanced assertion generation with:
// - Proper module structure
// - Clock domain handling
// - Reset consideration
// - Timing constraint validation
```

## 🛠️ Technical Improvements

### Build System
- **Modern tooling**: ESLint v9 with flat config format
- **Automated scripts**: Lint, build, and package automation
- **Icon integration**: Professional extension icon included
- **VSIX optimization**: Reduced package size with better file selection

### Project Structure
- **Clean organization**: Removed development artifacts and test files
- **Focused examples**: Curated sample files for learning
- **Proper .vscodeignore**: Optimized package content

## 📦 Package Information

- **Extension ID**: `waveform-render-sva-enhanced`
- **Version**: `0.27.0`
- **Publisher**: `MameMame777`
- **License**: MIT
- **Package Size**: 157.54 KB (32 files)

## 🎯 Compatibility

- **VS Code**: ^1.65.0
- **Node.js**: ^14.0.0
- **TypeScript**: ^4.9.4
- **Categories**: Programming Languages, Visualization, Other

## 🔄 Migration Guide

### From Previous Versions
- No breaking changes for existing WaveDrom JSON files
- Enhanced SVA generation with backward compatibility
- All existing keyboard shortcuts remain the same

### For Developers
- ESLint configuration updated (remove tslint dependencies)
- New logical operator syntax available but optional
- Enhanced error handling and reporting

## 🤝 Contributing

This release establishes a solid foundation for community contributions:
- Modern development environment
- Comprehensive testing framework
- Clear coding standards
- Detailed documentation

## 🙏 Acknowledgments

- **Borja Penuelas**: Original waveform-render-vscode creator
- **WaveDrom Community**: Timing diagram rendering engine
- **VS Code Team**: Extension development platform
- **SystemVerilog Community**: Hardware verification standards

---

**Download**: [waveform-render-sva-enhanced-0.27.0.vsix](https://github.com/MameMame777/WaveRenderSVA/releases/download/v0.27.0/waveform-render-sva-enhanced-0.27.0.vsix)

**Installation**: `code --install-extension waveform-render-sva-enhanced-0.27.0.vsix`
