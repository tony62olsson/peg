import abc
import ast
import re
import unittest


########################################################################################################################
import sys


def memoize(f):

    class Memoizer(dict):

        def __get__(self, obj, objtype):
            return lambda *args: self(obj, *args)

        def __call__(self, *args):
            return self[args]

        def __missing__(self, key):
            return self.setdefault(key, f(*key))

    return Memoizer()


def trace(f):

    class Tracer(object):

        def __get__(self, obj, objtype):
            return lambda *args, **kwargs: self(obj, *args, **kwargs)

        def __call__(self, *args, **kwargs):
            a = ', '.join([repr(i) for i in args] + ['%s=%s' % (k, repr(w)) for k,w in kwargs.items()])
            try:
                result = f(*args,**kwargs)
                print("%s(%s): ==> %s" % (f, a, repr(result)))
                return result
            except Exception as e:
                print("%s(%s): --> %s" % (f, a, repr(e)))
                raise

    return Tracer()


########################################################################################################################


class Grammar(object):
    """
Grammar:

* statement = name '=' rule
* rule = sequence {'/' sequence}
* sequence = {sequence_word} ['&' {sequence_word}+]
* sequence_word =  ['!'] word ['?' / '*' / '+' / '<' [lower] [',' [upper]] '>']
* word = regexp / string / name / '(' rule ')' / '{' rule '}' / '[' rule ']' / '<<' rule '>>

Literals:

* name = r'\w+'
* string = r"'(?:\\'|[^'])*'"
* regexp = r"r'(?:\\'|[^'])*'"

Skipped:

* r'\s*'

Repetition short-cuts:

* word? == word<0,1>
* word* == word<0,>
* word+ == word<1,>
* word<n> == word<n,n>
* word<n,m> ==

No skip rules:

* << rule >>    is rule with no skip
"""

    def __init__(self):
        names = dict()
        grammar_parser = GrammarParser()
        for name, func in self.__class__.__dict__.items():
            if name.startswith('rule_') or name.endswith('_rule'):
                name, rule = grammar_parser.parse(func.__doc__)
                names.setdefault(name, list()).append(rule)
        self.rules = dict((name, SelectionMatcher(*rules)) for name, rules in names.items())

    def parse(self, goal, text):
        result, end = ReferenceMatcher(goal).match(Context(self.rules, text), 0, RegexpMatcher(r'\s*'))
        if result is not None and end == len(text):
            return Matcher.apply(result, self)
        else:
            return None


########################################################################################################################


class GrammarParser(object):

    def __init__(self):
        self.rules = {
            'statement':
                Matcher.seq(r'/\w+/', '=', 'rule'),
            'rule':
                Matcher.seq('sequence', {('/', 'sequence')}),
            'sequence':
                Matcher.seq({'sequence_word'}, [('&', {1: 'sequence_word'})]),
            'sequence_word':
                Matcher.seq(['!'], 'word', ['counting']),
            'word':
                Matcher.sel('regexp', 'string', 'reference', 'group', 'repeat', 'optional', 'verbatim'),
            'counting':
                Matcher.sel('?', '*', '+', ('<', 'number', '>'), ('<', ['number'], ',', ['number'], '>')),
            'number':
                Matcher.seq(r'/\d+/'),
            'regexp':
                Matcher.seq(r"/r'(?:\\'|[^'])*'/"),
            'string':
                Matcher.seq(r"/'(?:\\'|[^'])*'/"),
            'reference':
                Matcher.seq(r'/\w+/'),
            'group':
                Matcher.seq('(', 'rule', ')'),
            'repeat':
                Matcher.seq('{', 'rule', '}'),
            'optional':
                Matcher.seq('[', 'rule', ']'),
            'verbatim':
                Matcher.seq('<<', 'rule', '>>')
        }

    def parse(self, text, goal='statement'):
        result, end = ReferenceMatcher(goal).match(Context(self.rules, text), 0, RegexpMatcher(r'\s*'))
        if result is not None and end == len(text):
            return Matcher.apply(result, self)
        else:
            return None

    def statement_visitor(self, args):
        name, _, rule = args
        return name.group(0), rule

    def rule_visitor(self, rule):
        selection, selections = rule
        if selections:
            return SelectionMatcher(selection, *list(sequence for _, sequence in selections))
        else:
            return selection

    def sequence_visitor(self, rule):
        sequence, lookahead = rule
        if len(lookahead) == 1:
           sequence.append(LookaheadMatcher(lookahead[0]))
        elif len(lookahead) > 1:
            sequence.append(LookaheadMatcher(SequenceMatcher(*lookahead)))
        if len(sequence) == 1:
            result = sequence[0]
        else:
            result = SequenceMatcher(*sequence)
        return result

    def sequence_word_visitor(self, rule):
        negator, word, counting = rule
        if counting:
            lower, upper = counting[0]
            word = RepeatMatcher(lower, upper, word)
        if negator:
            word = NotMatcher(word)
        return word

    def word_visitor(self, word):
        return word

    def counting_visitor(self, arg):
        if len(arg) == 2:
            token, _ = arg
            return {'?': (0, 1), '*': (0, None), '+': (1, None)}[token]
        elif len(arg) == 3:
            _, times, _ = arg
            return times, times
        else:
            _, lower, _, upper, _ = arg
            return (lower[0] if lower else 0), (upper[0] if upper else None)

    def reference_visitor(self, name):
        return ReferenceMatcher(name.group(0))

    def group_visitor(self, rule):
        return rule[1]

    def repeat_visitor(self, rule):
        return RepeatMatcher(0, None, rule[1])

    def optional_visitor(self, rule):
        return RepeatMatcher(0, 1, rule[1])

    def verbatim_visitor(self, rule):
        return VerbatimMatcher(rule[1])

    def string_visitor(self, value):
        return StringMatcher(ast.literal_eval(value.group(0)))

    def regexp_visitor(self, value):
        return RegexpMatcher(ast.literal_eval(value.group(0)))

    def number_visitor(self, value):
        return ast.literal_eval(value.group(0))


def ref(name):
    return ReferenceMatcher(name)


def opt(*matchers):
    return RepeatMatcher(0, 1, matchers[0] if len(matchers) == 1 else SequenceMatcher(*matchers))


def rep0(*matchers):
    return RepeatMatcher(0, None, matchers[0] if len(matchers) == 1 else SequenceMatcher(*matchers))


def rep1(*matchers):
    return RepeatMatcher(1, None, matchers[0] if len(matchers) == 1 else SequenceMatcher(*matchers))


########################################################################################################################


class Context(object):

    def __init__(self, rules, text):
        self.rules = rules
        self.text = text

    def __repr__(self):
        return "Context(%s)" % repr(self.text)


########################################################################################################################


class Matcher(object):

    @abc.abstractmethod
    def match(self, context, at, skip):
        raise NotImplemented()

    @classmethod
    def seq(cls, *args):
        if len(args) == 1:
            return cls._create(args[0])
        else:
            return SequenceMatcher(*list(cls._create(arg) for arg in args))

    @classmethod
    def sel(cls, *args):
        if len(args) == 1:
            return cls._create(args[0])
        else:
            return SelectionMatcher(*list(cls._create(arg) for arg in args))



    @classmethod
    def apply(cls, match, visitor):
        if type(match) == list:
            return list(cls.apply(item, visitor) for item in match)
        elif type(match) == tuple and not type(match[1]) == int:
            return cls._visit(visitor, match[0], cls.apply(match[1], visitor))
        else:
            return match

    @classmethod
    def _visit(cls, visitor, name, args):
        for suffix in ['_visitor', '_rule']:
            fn_name = name + suffix
            if fn_name in visitor.__class__.__dict__:
                return visitor.__class__.__dict__[fn_name](visitor, args)
        raise Exception("%s.%s do not have a '%s_visitor' or '%s_rule' method defined" %
                        (visitor.__class__.__module__, visitor.__class__.__name__, name, name))

    @staticmethod
    def _skip(context, at, skip):
        if skip:
            result, end = skip.match(context, at, None)
            while result and end > at:
                at = end
                result, end = skip.match(context, at, None)
        return at

    WORD_RE = re.compile(r'^\w+$')

    @classmethod
    def _create(cls, arg):
        if type(arg) == str:
            if cls.WORD_RE.match(arg):
                return ReferenceMatcher(arg)
            elif len(arg) > 2 and arg.startswith('/') and arg.endswith('/'):
                return RegexpMatcher(arg[1:-1])
            elif len(arg) > 2 and arg.startswith('<') and arg.endswith('>'):
                return StringMatcher(arg[1:-1])
            else:
                return StringMatcher(arg)
        elif type(arg) == tuple:
            return cls.seq(*arg)
        elif type(arg) == list and len(arg) == 1:
            return RepeatMatcher(0, 1, cls._create(arg[0]))
        elif type(arg) == set and len(arg) == 1:
            return RepeatMatcher(0, None, cls._create(arg.pop()))
        elif type(arg) == dict and len(arg) == 1:
            for key, value in arg.items():
                if type(key) == str:
                    return NamedMatcher(key, cls._create(value))
                elif type(key) == int:
                    return RepeatMatcher(key, None, cls._create(value))
                elif type(key) == tuple:
                    return RepeatMatcher(key[0], key[1], cls._create(value))
        elif isinstance(arg, Matcher):
            return arg
        raise Exception("malformed Matcher.seq or Matcher.sel item: " + repr(arg))



class ReferenceMatcher(Matcher):

    def __init__(self, name):
        self.name = name

    @memoize
    def match(self, context, at, skip):
        if self.name in context.rules:
            result, end = context.rules[self.name].match(context, at, skip)
            if result:
                return (self.name, result), end
        return None, at

    def __eq__(self, other):
        return type(other) == ReferenceMatcher and other.name == self.name

    def __hash__(self):
        return hash(self.name)

    def __str__(self):
        return self.name

    def __repr__(self):
        return "ReferenceMatcher(%s)" % self.name


class NamedMatcher(Matcher):

    def __init__(self, name, rule):
        self.name = name
        self.rule = rule

    @memoize
    def match(self, context, at, skip):
        result, end = self.rule.match(context, at, skip)
        if result:
            return (self.name, result), end
        return None, at

    def __eq__(self, other):
        return type(other) == NamedMatcher and other.name == self.name and other.rule == self.rule

    def __hash__(self):
        return hash((self.name, self.rule))

    def __str__(self):
        return "%s:%s" % (self.name, self.rule)

    def __repr__(self):
        return "NamedMatcher(%s, %s)" % (self.name, repr(self.rule))


class StringMatcher(Matcher):

    def __init__(self, word):
        self.word = word
        self.length = len(word)

    @memoize
    def match(self, context, at, skip):
        at = self._skip(context, at, skip)
        if context.text.startswith(self.word, at):
            return (self.word, at), at + self.length
        return None, at

    def __eq__(self, other):
        return type(other) == StringMatcher and other.word == self.word

    def __hash__(self):
        return hash(self.word)

    def __str__(self):
        return repr(self.word)

    def __repr__(self):
        return "StringMatcher(%s)" % repr(self.word)


class RegexpMatcher(Matcher):

    def __init__(self, regexp):
        self.regexp = regexp if type(regexp) == type(re.compile('')) else re.compile(str(regexp))

    @memoize
    def match(self, context, at, skip):
        at = self._skip(context, at, skip)
        match = self.regexp.match(context.text, at)
        if match:
            return match, match.end(0)
        return None, at

    def __eq__(self, other):
        return type(other) == RegexpMatcher and other.regexp == self.regexp

    def __hash__(self):
        return hash(self.regexp)

    def __str__(self):
        return 'r' + repr(self.regexp.pattern)

    def __repr__(self):
        return "RegexpMatcher(%s)" % repr(self.regexp.pattern)


class SelectionMatcher(Matcher):

    def __init__(self, *matchers):
        self.matchers = matchers

    @memoize
    def match(self, context, at, skip):
        for matcher in self.matchers:
            result, end = matcher.match(context, at, skip)
            if result is not None:
                return result, end
        return None, at

    def __eq__(self, other):
        return type(other) == SelectionMatcher and other.matchers == self.matchers

    def __hash__(self):
        return hash(self.matchers)

    def __str__(self):
        return ' / '.join(str(r) for r in self.matchers)

    def __repr__(self):
        return "SelectionMatcher(%s)" % ', '.join(repr(r) for r in self.matchers)


class SequenceMatcher(Matcher):

    def __init__(self, *matchers):
        self.matchers = matchers

    @memoize
    def match(self, context, at, skip):
        sequence = list()
        end = at
        for matcher in self.matchers:
            result, end = matcher.match(context, end, skip)
            if result is None:
                return None, at
            if type(result) != bool:
                sequence.append(result)
        return sequence, end

    def __eq__(self, other):
        return type(other) == SequenceMatcher and other.matchers == self.matchers

    def __hash__(self):
        return hash(self.matchers)

    def __str__(self):
        return "(%s)" % ' '.join(str(r) for r in self.matchers)

    def __repr__(self):
        return "SequenceMatcher(%s)" % ', '.join(repr(r) for r in self.matchers)


class RepeatMatcher(Matcher):

    def __init__(self, lower, upper, matcher):
        self.lower = lower
        self.upper = upper
        self.matcher = matcher

    @memoize
    def match(self, context, at, skip):
        sequence = list()
        end = at
        while self.upper is None or len(sequence) < self.upper:
            result, end = self.matcher.match(context, end, skip)
            if result is None:
                break
            sequence.append(result)
        if len(sequence) < self.lower:
            return None, at
        return sequence, end

    def __eq__(self, other):
        return type(other) == RepeatMatcher and other.lower == self.lower and other.upper == self.upper and other.matcher == self.matcher

    def __hash__(self):
        return hash((self.lower, self.upper, self.matcher))

    def __str__(self):
        if self.lower == 0 and self.upper is None:
            return "{%s}" % self.matcher
        elif self.lower == 0 and self.upper == 1:
            return "[%s]" % self.matcher
        elif self.lower == 0:
            return "{%s}<,%d>" % (self.matcher, self.upper)
        elif self.upper is None:
            return "{%s}<%d,>" % (self.matcher, self.lower)
        else:
            return "{%s}<%d,%d>" % (self.matcher, self.lower, self.upper)

    def __repr__(self):
        return "RepeatMatcher(%s, %s, %s)" % (self.lower, self.upper, repr(self.matcher))


class LookaheadMatcher(Matcher):

    def __init__(self, matcher):
        self.matcher = matcher

    @memoize
    def match(self, context, at, skip):
        result, _ = self.matcher.match(context, at, skip)
        return result is not None or None, at

    def __eq__(self, other):
        return type(other) == LookaheadMatcher and other.matcher == self.matcher

    def __hash__(self):
        return hash(self.matcher)

    def __str__(self):
        return "& %s" % self.matcher

    def __repr__(self):
        return "LookaheadMatcher(%s)" % repr(self.matcher)


class NotMatcher(Matcher):

    def __init__(self, matcher):
        self.matcher = matcher

    @memoize
    def match(self, context, at, skip):
        result, end = self.matcher.match(context, at, skip)
        return result is None or None, at

    def __eq__(self, other):
        return type(other) == NotMatcher and other.matcher == self.matcher

    def __hash__(self):
        return hash(self.matcher)

    def __str__(self):
        return "& %s" % self.matcher

    def __repr__(self):
        return "NotMatcher(%s)" % repr(self.matcher)


class VerbatimMatcher(Matcher):

    def __init__(self, matcher):
        self.matcher = matcher

    @memoize
    def match(self, context, at, skip):
        return self.matcher.match(context, at, None)

    def __eq__(self, other):
        return type(other) == VerbatimMatcher and other.matcher == self.matcher

    def __hash__(self):
        return hash(self.matcher)

    def __str__(self):
        return "<<%s>>" % self.matcher

    def __repr__(self):
        return "VerbatimMatcher(%s)" % repr(self.matcher)


########################################################################################################################


def re_str(result):
    return re_str_iter(result[0]), result[1]


def re_str_iter(result):
    if result is None or type(result) == bool:
        return result
    elif type(result) == tuple:
        if type(result[1]) == int:
            return result
        else:
            return result[0], re_str_iter(result[1])
    elif type(result) == list:
        return list(re_str_iter(item) for item in result)
    else:
        return result.start(0), result.group(0)


class TestMatchers(unittest.TestCase):

    skip = RegexpMatcher(r'\s+')

    def test_string_matcher(self):
        matcher = StringMatcher('hello')
        self.assertEqual(matcher.match(Context(None, "hello"), 0, self.skip),
                         (('hello', 0), 5))
        self.assertEqual(matcher.match(Context(None, " \n\thello"), 0, self.skip),
                         (('hello', 3), 8))
        self.assertEqual(matcher.match(Context(None, "Hello"), 0, self.skip),
                         (None, 0))
        self.assertEqual(matcher.match(Context(None, "hello"), 1, self.skip),
                         (None, 1))
        self.assertEqual(matcher.match(Context(None, "hello"), 9, self.skip),
                         (None, 9))

    def test_regexp_matcher(self):
        matcher = RegexpMatcher(re.compile('hello', re.IGNORECASE))
        self.assertEqual(re_str(matcher.match(Context(None, "hello"), 0, self.skip)),
                         ((0, 'hello'), 5))
        self.assertEqual(re_str(matcher.match(Context(None, " \n\thello"), 0, self.skip)),
                         ((3, 'hello'), 8))
        self.assertEqual(re_str(matcher.match(Context(None, "Hello"), 0, self.skip)),
                         ((0, 'Hello'), 5))
        self.assertEqual(re_str(matcher.match(Context(None, "HELLO"), 0, self.skip)),
                         ((0, 'HELLO'), 5))
        self.assertEqual(matcher.match(Context(None, "hell"), 0, self.skip),
                         (None, 0))
        self.assertEqual(matcher.match(Context(None, "hello"), 1, self.skip),
                         (None, 1))
        self.assertEqual(matcher.match(Context(None, "hello"), 9, self.skip),
                         (None, 9))

    def test_selection_matcher(self):
        matcher = SelectionMatcher(StringMatcher('hello'), StringMatcher('world'))
        self.assertEqual(matcher.match(Context(None, "hello"), 0, self.skip),
                         (('hello', 0), 5))
        self.assertEqual(matcher.match(Context(None, "world"), 0, self.skip),
                         (('world', 0), 5))
        self.assertEqual(matcher.match(Context(None, ""), 0, self.skip),
                         (None, 0))

    def test_sequence_matcher(self):
        matcher = SequenceMatcher(StringMatcher('hello'), StringMatcher('world'))
        self.assertEqual(matcher.match(Context(None, "hello world"), 0, self.skip),
                         ([('hello', 0), ('world', 6)], 11))
        self.assertEqual(matcher.match(Context(None, "hello"), 0, self.skip),
                         (None, 0))
        self.assertEqual(matcher.match(Context(None, "world"), 0, self.skip),
                         (None, 0))

    def test_repeat_matcher(self):
        matcher = RepeatMatcher(2, 5, StringMatcher('a'))
        self.assertEqual(matcher.match(Context(None, ""), 0, self.skip),
                         (None, 0))
        self.assertEqual(matcher.match(Context(None, "a"), 0, self.skip),
                         (None, 0))
        self.assertEqual(matcher.match(Context(None, "aa"), 0, self.skip),
                         ([('a', 0), ('a', 1)], 2))
        self.assertEqual(matcher.match(Context(None, "aaa"), 0, self.skip),
                         ([('a', 0), ('a', 1), ('a', 2)], 3))
        self.assertEqual(matcher.match(Context(None, "aaaa"), 0, self.skip),
                         ([('a', 0), ('a', 1), ('a', 2), ('a', 3)], 4))
        self.assertEqual(matcher.match(Context(None, "aaaaa"), 0, self.skip),
                         ([('a', 0), ('a', 1), ('a', 2), ('a', 3), ('a', 4)], 5))
        self.assertEqual(matcher.match(Context(None, "aaaaaa"), 0, self.skip),
                         ([('a', 0), ('a', 1), ('a', 2), ('a', 3), ('a', 4)], 5))
        self.assertEqual(matcher.match(Context(None, "aaaaaaa"), 3, self.skip),
                         ([('a', 3), ('a', 4), ('a', 5), ('a', 6)], 7))

    def test_reference_matcher(self):
        matchers = {'word': RegexpMatcher(r'\w+')}
        matcher = ReferenceMatcher('word')
        self.assertEqual(re_str(matcher.match(Context(matchers, "hello"), 0, self.skip)),
                         (('word', (0, 'hello')), 5))
        self.assertEqual(matcher.match(Context(matchers, "..."), 0, self.skip),
                         (None, 0))
        self.assertEqual(matcher.match(Context({}, "hello"), 0, self.skip),
                         (None, 0))

    def test_named_matcher(self):
        matcher = NamedMatcher('word', RegexpMatcher(r'\w+'))
        self.assertEqual(re_str(matcher.match(Context(None, "hello"), 0, self.skip)),
                         (('word', (0, 'hello')), 5))
        self.assertEqual(matcher.match(Context(None, "..."), 0, self.skip),
                         (None, 0))

    def test_lookahead_matcher(self):
        matcher = LookaheadMatcher(StringMatcher('hello'))
        self.assertEqual(matcher.match(Context(None, "hello"), 0, self.skip),
                         (True, 0))
        self.assertEqual(matcher.match(Context(None, "world"), 0, self.skip),
                         (None, 0))
        extended_matcher = SequenceMatcher(matcher, RegexpMatcher('.*'))
        self.assertEqual(re_str(extended_matcher.match(Context(None, "hello world"), 0, self.skip)),
                         ([(0, 'hello world')], 11))
        self.assertEqual(extended_matcher.match(Context(None, "world hello"), 0, self.skip),
                         (None, 0))

    def test_not_matcher(self):
        matcher = NotMatcher(StringMatcher('world'))
        self.assertEqual(matcher.match(Context(None, "hello"), 0, self.skip),
                         (True, 0))
        self.assertEqual(matcher.match(Context(None, "world"), 0, self.skip),
                         (None, 0))
        extended_matcher = SequenceMatcher(matcher, RegexpMatcher('.*'))
        self.assertEqual(re_str(extended_matcher.match(Context(None, "hello world"), 0, self.skip)),
                         ([(0, 'hello world')], 11))
        self.assertEqual(extended_matcher.match(Context(None, "world hello"), 0, self.skip),
                         (None, 0))

    def test_verbatim_matcher(self):
        matcher = StringMatcher('hello')
        self.assertEqual(VerbatimMatcher(matcher).match(Context(None, "hello"), 0, self.skip),
                         (('hello', 0), 5))
        self.assertEqual(matcher.match(Context(None, " hello"), 0, self.skip),
                         (('hello', 1), 6))
        self.assertEqual(VerbatimMatcher(matcher).match(Context(None, " hello"), 0, self.skip),
                         (None, 0))


class TestGrammarParser(unittest.TestCase):

    def test_word_rule(self):
        grammar = GrammarParser()
        self.assertEqual(grammar.parse("hello", goal='word'),
                         ReferenceMatcher('hello'))
        self.assertEqual(grammar.parse("'hello world'", goal='word'),
                         StringMatcher('hello world'))
        self.assertEqual(grammar.parse("r'hello\s+world'", goal='word'),
                         RegexpMatcher(r'hello\s+world'))
        self.assertEqual(grammar.parse("(x)", goal='word'),
                         ReferenceMatcher('x'))
        self.assertEqual(grammar.parse("{x x}", goal='word'),
                         RepeatMatcher(0, None, SequenceMatcher(ReferenceMatcher('x'), ReferenceMatcher('x'))))
        self.assertEqual(grammar.parse("[x / x]", goal='word'),
                         RepeatMatcher(0, 1, SelectionMatcher(ReferenceMatcher('x'), ReferenceMatcher('x'))))
        self.assertEqual(grammar.parse("<<x>>", goal='word'),
                         VerbatimMatcher(ReferenceMatcher('x')))

    def test_sequence_word_rule(self):
        grammar = GrammarParser()
        self.assertEqual(grammar.parse("x", goal='sequence_word'),
                         ReferenceMatcher('x'))
        self.assertEqual(grammar.parse("!x", goal='sequence_word'),
                         NotMatcher(ReferenceMatcher('x')))
        self.assertEqual(grammar.parse("x?", goal='sequence_word'),
                         RepeatMatcher(0, 1, ReferenceMatcher('x')))
        self.assertEqual(grammar.parse("x*", goal='sequence_word'),
                         RepeatMatcher(0, None, ReferenceMatcher('x')))
        self.assertEqual(grammar.parse("x+", goal='sequence_word'),
                         RepeatMatcher(1, None, ReferenceMatcher('x')))
        self.assertEqual(grammar.parse("x<3>", goal='sequence_word'),
                         RepeatMatcher(3, 3, ReferenceMatcher('x')))
        self.assertEqual(grammar.parse("x<,3>", goal='sequence_word'),
                         RepeatMatcher(0, 3, ReferenceMatcher('x')))
        self.assertEqual(grammar.parse("x<3,>", goal='sequence_word'),
                         RepeatMatcher(3, None, ReferenceMatcher('x')))
        self.assertEqual(grammar.parse("x<,>", goal='sequence_word'),
                         RepeatMatcher(0, None, ReferenceMatcher('x')))
        self.assertEqual(grammar.parse("x<5,7>", goal='sequence_word'),
                         RepeatMatcher(5, 7, ReferenceMatcher('x')))
        # ...


class TestGrammar(unittest.TestCase):

    class HelloGrammar(Grammar):

        def statement_rule(self, args):
            r"statement = {r'\w+'}"
            return tuple(arg[0] for arg in args)

        # ...

    def test_simple_grammar(self):
        grammar = self.HelloGrammar()
        self.assertEqual(grammar.parse("statement", "hello"), ('hello',))
        self.assertEqual(grammar.parse("statement", "hello world"), ('hello', 'world'))
        self.assertEqual(grammar.parse("statement", "hello world!"), None)
        # ...
