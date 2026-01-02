/**
 * PrismJS syntax highlighting for sMRD/MoRDor Litmus Tests
 * Based on lexer.mll and parser.mly grammar files
 */

(function (Prism) {
	Prism.languages.smrd = {
		// Comments
		'comment': {
			pattern: /\/\/.*$/m,
			greedy: true
		},

		// Backtick labels (labels for statements)
		'label': {
			pattern: /`[^`]*`/,
			greedy: true
		},

		// String literals
		'string': {
			pattern: /"[^"]*"/,
			greedy: true
		},

		// Memory ordering and assignment operators (must come before other operators)
		'memory-operator': {
			pattern: /:(?:v(?:rlx|rel|acq|sc)?|rlx|rel|acq|sc)?=/,
			alias: 'operator'
		},

		// Keywords - Memory orderings
		'memory-order': {
			pattern: /\b(?:nonatomic|na|relaxed|rlx|release|rel|acquire|acq|relacq|sequentially_consistent|sc|strong|normal)\b/,
			alias: 'keyword'
		},

		// Keywords - Operations
		'operation': {
			pattern: /\b(?:FADD|fadd|CAS|cas|fence|malloc|free|lock|unlock|load|store|skip)\b/,
			alias: 'keyword'
		},

		// Keywords - Control flow
		'control-flow': {
			pattern: /\b(?:if|else|while|do)\b/,
			alias: 'keyword'
		},

		// Keywords - Configuration
		'config-keyword': {
			pattern: /\b(?:allow|forbid|name|model|values|forall)\b/,
			alias: 'keyword'
		},

		// Special operators
		'special-operator': [
			{
				pattern: /~~~?>/,
				alias: 'operator'
			},
			{
				pattern: /\[\[|\]\]/,
				alias: 'punctuation'
			},
			{
				pattern: /\|\|\|/,
				alias: 'operator'
			}
		],

		// Logical and comparison operators
		'operator': [
			/!=|==|>=|<=|&&|\|\||\\?(?:not)?\bin\b|[∈∉]/,
			/[+\-*/%><=!&|^~]/
		],

		// Assignment operator
		'assignment': {
			pattern: /:=/,
			alias: 'operator'
		},

		// Numbers (decimal and hexadecimal)
		'number': /\b(?:0x[\da-fA-F]+|\d+)\b/,

		// Registers (start with 'r' followed by alphanumeric)
		'register': {
			pattern: /\br[\w]+\b/,
			alias: 'variable'
		},

		// AtLoc variables (start with '@')
		'atloc': {
			pattern: /@[\w]+/,
			alias: 'variable'
		},

		// Global variables (identifiers starting with letter or underscore)
		'global': {
			pattern: /\b[a-zA-Z_][\w]*\b/,
			lookbehind: true,
			alias: 'variable'
		},

		// Punctuation and delimiters
		'punctuation': /[(){}\[\];,.!&^|~'_]/,

		// Special symbols
		'arrow': {
			pattern: /~~>/,
			alias: 'operator'
		},

		// Dereference operator
		'dereference': {
			pattern: /\*/,
			alias: 'operator'
		}
	};

	// Alias for convenience
	Prism.languages.litmus = Prism.languages.smrd;
	Prism.languages.mordor = Prism.languages.smrd;

}(Prism));

console.log("Prism sMRD language definition loaded");
