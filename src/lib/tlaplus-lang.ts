import { StreamLanguage, LanguageSupport } from '@codemirror/language';

const tlaKeywords = new Set([
  'MODULE', 'EXTENDS', 'VARIABLES', 'VARIABLE', 'CONSTANTS', 'CONSTANT',
  'ASSUME', 'ASSUMPTION', 'AXIOM', 'THEOREM', 'LEMMA', 'PROPOSITION',
  'INSTANCE', 'LOCAL', 'LET', 'IN', 'IF', 'THEN', 'ELSE', 'CASE',
  'OTHER', 'CHOOSE', 'EXCEPT', 'WITH', 'DOMAIN', 'SUBSET', 'UNION',
  'ENABLED', 'UNCHANGED', 'SF_', 'WF_', 'TRUE', 'FALSE', 'BOOLEAN',
  'STRING', 'ACTION', 'RECURSIVE', 'NEW', 'DEFINE', 'PROOF', 'BY',
  'QED', 'OBVIOUS', 'OMITTED', 'HAVE', 'TAKE', 'SUFFICES', 'PICK',
  'WITNESS', 'USE', 'DEF', 'DEFS', 'HIDE',
]);

const cfgKeywords = new Set([
  'INIT', 'NEXT', 'SPECIFICATION', 'INVARIANT', 'INVARIANTS',
  'PROPERTY', 'PROPERTIES', 'CONSTANT', 'CONSTANTS',
  'CONSTRAINT', 'CONSTRAINTS', 'ACTION_CONSTRAINT', 'ACTION_CONSTRAINTS',
  'SYMMETRY', 'VIEW', 'TYPE', 'TYPE_CONSTRAINT',
  'CHECK_DEADLOCK', 'ALIAS',
]);

const tlaStreamParser = {
  startState() {
    return { inComment: false, commentDepth: 0 };
  },
  token(stream: any, state: any): string | null {
    // Block comment
    if (state.inComment) {
      while (!stream.eol()) {
        if (stream.match('*)')) {
          state.commentDepth--;
          if (state.commentDepth === 0) {
            state.inComment = false;
            return 'comment';
          }
        } else if (stream.match('(*')) {
          state.commentDepth++;
        } else {
          stream.next();
        }
      }
      return 'comment';
    }

    // Start of block comment
    if (stream.match('(*')) {
      state.inComment = true;
      state.commentDepth = 1;
      while (!stream.eol()) {
        if (stream.match('*)')) {
          state.commentDepth--;
          if (state.commentDepth === 0) {
            state.inComment = false;
            return 'comment';
          }
        } else if (stream.match('(*')) {
          state.commentDepth++;
        } else {
          stream.next();
        }
      }
      return 'comment';
    }

    // Line comment
    if (stream.match('\\*')) {
      stream.skipToEnd();
      return 'comment';
    }

    // Module header/footer lines
    if (stream.match(/^-{4,}\s*MODULE\b/)) {
      stream.skipToEnd();
      return 'keyword';
    }
    if (stream.match(/^={4,}/)) {
      stream.skipToEnd();
      return 'keyword';
    }
    if (stream.match(/^-{4,}/)) {
      return 'keyword';
    }

    // Skip whitespace
    if (stream.eatSpace()) return null;

    // Strings
    if (stream.match('"')) {
      while (!stream.eol()) {
        if (stream.next() === '"') break;
      }
      return 'string';
    }

    // Numbers
    if (stream.match(/^\d+/)) return 'number';

    // Operators
    if (stream.match(/^(\\in|\\notin|\\subseteq|\\cup|\\cap|\\setminus|\\times)/)) return 'operator';
    if (stream.match(/^(\\A|\\E|\\AA|\\EE)/)) return 'operator';
    if (stream.match(/^(\/\\|\\\/|=>|~|<=>|#)/)) return 'operator';
    if (stream.match(/^(<<|>>)/)) return 'bracket';
    if (stream.match(/^(->|<-|\|->)/)) return 'operator';
    if (stream.match(/^(==|:=|')/)) return 'operator';
    if (stream.match(/^(\[\]|<>)/)) return 'operator';

    // Words
    if (stream.match(/^[A-Za-z_]\w*/)) {
      const word = stream.current();
      if (tlaKeywords.has(word)) return 'keyword';
      // Uppercase identifiers that look like operators/definitions
      if (word === word.toUpperCase() && word.length > 1) return 'variableName.special';
      return 'variableName';
    }

    stream.next();
    return null;
  },
};

const cfgStreamParser = {
  startState() { return {}; },
  token(stream: any): string | null {
    // Line comment
    if (stream.match('\\*')) {
      stream.skipToEnd();
      return 'comment';
    }
    if (stream.eatSpace()) return null;
    if (stream.match(/^[A-Za-z_]\w*/)) {
      const word = stream.current();
      if (cfgKeywords.has(word)) return 'keyword';
      if (word === 'TRUE' || word === 'FALSE') return 'bool';
      return 'variableName';
    }
    if (stream.match(/^\d+/)) return 'number';
    if (stream.match('"')) {
      while (!stream.eol()) {
        if (stream.next() === '"') break;
      }
      return 'string';
    }
    stream.next();
    return null;
  },
};

const tlaLanguage = StreamLanguage.define(tlaStreamParser);
const cfgLanguage = StreamLanguage.define(cfgStreamParser);

export function tlaplus() {
  return new LanguageSupport(tlaLanguage);
}

export function tlaCfg() {
  return new LanguageSupport(cfgLanguage);
}
