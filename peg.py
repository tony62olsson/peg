import abc
import ast
import re
import unittest


########################################################################################################################


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
        return self.rules.setdefault(goal, SelectionMatcher()).match(Context(self, text), 0, None)


########################################################################################################################


class GrammarParser(object):

    def __init__(self):
        self.name = self._name_matcher()
        self.string = self._string_matcher()
        self.regexp = self._regexp_matcher()
        self.number = self._number_matcher()
        self.rules = {
            'statement': self._statement_matcher(),
            'rule': self._rule_matcher(),
            'sequence': self._sequence_matcher(),
            'sequence_word': self._sequence_word_matcher(),
            'word': self._word_matcher()
        }

    #@trace
    def parse(self, text, goal='statement'):
        match = self.rules[goal].match(Context(self.rules, text), 0, RegexpMatcher(r'\s*'))
        if match:
            return match.apply()

    def _statement_matcher(self):
        # statement = word '=' rule

        def statement_action(r):
            return r[0].apply(), r[2].apply()

        return SequenceMatcher(self.name, StringMatcher('='), ref('rule'),
                               action=statement_action)

    def _rule_matcher(self):
        # rule = sequence {'/' sequence}

        def rule_action(r):
            r0 = r[0].apply()
            r1 = r[1].apply()
            if r1:
                return SelectionMatcher(r0, *r1)
            else:
                return r0

        m0 = ref('sequence')
        m1 = rep0(StringMatcher('/'), ref('sequence'), action=lambda r: r[1].apply())
        return SequenceMatcher(m0, m1, action=rule_action)

    def _sequence_matcher(self):
        # sequence = {sequence_word} ['&' {sequence_word}+]

        def sequence_action(r):
            r0 = r[0].apply()
            r1 = r[1].apply()
            if len(r0) == 1:
                return r0[0]
            else:
                return SequenceMatcher(*r0)

        m0 = rep0(ref('sequence_word'))
        m1 = opt(StringMatcher('&'), rep1(ref('sequence_word')))
        return SequenceMatcher(m0, m1, action=sequence_action)

    def _sequence_word_matcher(self):
        # sequence_word = ['!'] word ['?' | '*' | '+' | '<' times '>' | '<' [lower] ',' [upper] '>'

        def sequence_word_action(r):
            r0 = r[0].apply()
            matcher = r[1].apply()
            r2 = r[2].apply()
            if r2:
                matcher = RepeatMatcher(r2[0][0], r2[0][1], matcher)
            if r0:
                matcher = NotMatcher(matcher)
            return matcher

        m0 = opt(StringMatcher('!'))
        m1 = ref('word')
        m2s0 = StringMatcher('?', action=lambda _: (0, 1))
        m2s1 = StringMatcher('*', action=lambda _: (0, None))
        m2s2 = StringMatcher('+', action=lambda _: (1, None))
        m2s3a = SequenceMatcher(opt(self.number), StringMatcher(','), opt(self.number),
                               action=lambda r: ((lambda r0, r2: (r0[0] if r0 else 0, r2[0] if r2 else None))(r[0].apply(), r[2].apply())))
        m2s3b = SequenceMatcher(self.number, action=lambda r: (r[0].apply(), r[0].apply()))
        m2s3 = SequenceMatcher(StringMatcher('<'), SelectionMatcher(m2s3a, m2s3b), StringMatcher('>'),
                               action=lambda r: r[1].apply())
        m2 = opt(SelectionMatcher(m2s0, m2s1, m2s2, m2s3))
        return SequenceMatcher(m0, m1, m2, action=sequence_word_action)

    def _word_matcher(self):
        return SelectionMatcher(self.regexp,
                                self.string,
                                SequenceMatcher(self.name, action=lambda r: ref(r[0].apply())),
                                SequenceMatcher(StringMatcher('('), ref('rule'), StringMatcher(')'), action=lambda r: r[1].apply()),
                                SequenceMatcher(StringMatcher('{'), ref('rule'), StringMatcher('}'), action=lambda r: rep0(r[1].apply())),
                                SequenceMatcher(StringMatcher('['), ref('rule'), StringMatcher(']'), action=lambda r: opt(r[1].apply())),
                                SequenceMatcher(StringMatcher('<<'), ref('rule'), StringMatcher('>>'), action=lambda r: r[1].apply()))

    def _name_matcher(self):
        return RegexpMatcher(r'\w+', action=lambda r: r.group(0))

    def _string_matcher(self):
        return RegexpMatcher(r"'(?:\\'|[^'])*'", action=lambda r: StringMatcher(ast.literal_eval(r.group(0))))

    def _regexp_matcher(self):
        return RegexpMatcher(r"r'(?:\\'|[^'])*'", action=lambda r: RegexpMatcher(ast.literal_eval(r.group(0))))

    def _number_matcher(self):
        return RegexpMatcher('\d+', action=lambda r: ast.literal_eval(r.group(0)))


def ref(name, action=None):
    return ReferenceMatcher(name, action=action)


def opt(*matchers, action=None):
    return RepeatMatcher(0, 1, matchers[0] if len(matchers) == 1 else SequenceMatcher(*matchers, action=action))


def rep0(*matchers, action=None):
    return RepeatMatcher(0, None, matchers[0] if len(matchers) == 1 else SequenceMatcher(*matchers, action=action))


def rep1(*matchers, action=None):
    return RepeatMatcher(1, None, matchers[0] if len(matchers) == 1 else SequenceMatcher(*matchers, action=action))


########################################################################################################################


class Context(object):

    def __init__(self, rules, text):
        self.rules = rules
        self.text = text

    def __repr__(self):
        return "Context(%s)" % repr(self.text)


########################################################################################################################


class Result(object):

    def __init__(self, action, result, text, start, end):
        self.action = action
        self.result = result
        self.text = text
        self.start = start
        self.end = end

    #@trace
    def apply(self):
        if self.action:
            return self.action(self.result)
        elif type(self.result) == list:
            return list(r.apply() for r in self.result)
        elif type(self.result) == Result:
            return self.result.apply()
        else:
            return self

    def __str__(self):
        return self.text[self.start:self.end]

    def __repr__(self):
        return "Result(%s, %s, %s, <%d,%d>)" % (self.action, repr(self.result), repr(self.text[self.start:self.end]), self.start, self.end)


########################################################################################################################


class Matcher(object):

    @abc.abstractmethod
    def match(self, context, at, skip):
        raise NotImplemented()


class ReferenceMatcher(Matcher):

    def __init__(self, name, action=None):
        self.action = action
        self.name = name

    @memoize
    def match(self, context, at, skip):
        if self.name in context.rules:
            result = context.rules[self.name].match(context, at, skip)
            if result:
                return Result(self.action, result, context.text, at, result.end)

    def __eq__(self, other):
        return type(other) == ReferenceMatcher and other.name == self.name

    def __hash__(self):
        return hash(self.name)

    def __str__(self):
        return self.name

    def __repr__(self):
        return "ReferenceMatcher(%s)" % self.name


class StringMatcher(Matcher):

    def __init__(self, word, action=None):
        self.action = action
        self.word = word
        self.length = len(word)

    @memoize
    def match(self, context, at, skip):
        if skip:
            result = skip.match(context, at, None)
            while result and result.end > at:
                at = result.end
                result = skip.match(context, at, None)
        if context.text.startswith(self.word, at):
            return Result(self.action, self.word, context.text, at, at + self.length)

    def __eq__(self, other):
        return type(other) == StringMatcher and other.word == self.word

    def __hash__(self):
        return hash(self.word)

    def __str__(self):
        return repr(self.word)

    def __repr__(self):
        return "StringMatcher(%s)" % repr(self.word)


class RegexpMatcher(Matcher):

    def __init__(self, regexp, action=None):
        self.action = action
        self.regexp = regexp if type(regexp) == type(re.compile('')) else re.compile(str(regexp))

    @memoize
    def match(self, context, at, skip):
        if skip:
            result = skip.match(context, at, None)
            while result and result.end > at:
                at = result.end
                result = skip.match(context, at, None)
        match = self.regexp.match(context.text, at)
        if match:
            return Result(self.action, match, context.text, at, match.end(0))
        else:
            return None

    def __eq__(self, other):
        return type(other) == RegexpMatcher and other.regexp == self.regexp

    def __hash__(self):
        return hash(self.regexp)

    def __str__(self):
        return 'r' + repr(self.regexp.pattern)

    def __repr__(self):
        return "RegexpMatcher(%s)" % repr(self.regexp.pattern)


class SelectionMatcher(Matcher):

    def __init__(self, *matchers, action=None):
        self.action = action
        self.matchers = matchers

    @memoize
    def match(self, context, at, skip):
        for matcher in self.matchers:
            result = matcher.match(context, at, skip)
            if result is not None:
                return Result(self.action, result, context.text, at, result.end)
        return None

    def __eq__(self, other):
        return type(other) == SelectionMatcher and other.matchers == self.matchers

    def __hash__(self):
        return hash(self.matchers)

    def __str__(self):
        return ' / '.join(str(r) for r in self.matchers)

    def __repr__(self):
        return "SelectionMatcher(%s)" % ', '.join(repr(r) for r in self.matchers)


class SequenceMatcher(Matcher):

    def __init__(self, *matchers, action=None):
        self.action = action
        self.matchers = matchers

    @memoize
    def match(self, context, at, skip):
        sequence = list()
        end = at
        for matcher in self.matchers:
            result = matcher.match(context, end, skip)
            if result is None:
                return None
            end = result.end
            sequence.append(result)
        return Result(self.action, sequence, context.text, at, end)

    def __eq__(self, other):
        return type(other) == SequenceMatcher and other.matchers == self.matchers

    def __hash__(self):
        return hash(self.matchers)

    def __str__(self):
        return "(%s)" % ' '.join(str(r) for r in self.matchers)

    def __repr__(self):
        return "SequenceMatcher(%s)" % ', '.join(repr(r) for r in self.matchers)


class RepeatMatcher(Matcher):

    def __init__(self, lower, upper, matcher, action=None):
        self.action = action
        self.lower = lower
        self.upper = upper
        self.matcher = matcher

    @memoize
    def match(self, context, at, skip):
        end = at
        sequence = list()
        count = 0
        result = self.matcher.match(context, end, skip)
        while result:
            end = result.end
            if count == self.upper:
                return None
            sequence.append(result)
            count += 1
            result = self.matcher.match(context, end, skip)
        if count < self.lower:
            return None
        return Result(self.action, sequence, context.text, at, end)

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

    def __init__(self, matcher, action=None):
        self.action = action
        self.matcher = matcher

    @memoize
    def match(self, context, at, skip):
        result = self.matcher.match(context, at, skip)
        if result:
            return Result(self.action, result, context.text, at, at)

    def __eq__(self, other):
        return type(other) == LookaheadMatcher and other.matcher == self.matcher

    def __hash__(self):
        return hash(self.matcher)

    def __str__(self):
        return "& %s" % self.matcher

    def __repr__(self):
        return "LookaheadMatcher(%s)" % repr(self.matcher)


class NotMatcher(Matcher):

    def __init__(self, matcher, action=None):
        self.action = action
        self.matcher = matcher

    @memoize
    def match(self, context, at, skip):
        result = self.matcher.match(context, at, skip)
        if result is None:
            return Result(self.action, result, context.text, at, at)

    def __eq__(self, other):
        return type(other) == NotMatcher and other.matcher == self.matcher

    def __hash__(self):
        return hash(self.matcher)

    def __str__(self):
        return "& %s" % self.matcher

    def __repr__(self):
        return "NotMatcher(%s)" % repr(self.matcher)


class VerbatimMatcher(Matcher):

    def __init__(self, matcher, action=None):
        self.action = action
        self.matcher = matcher

    @memoize
    def match(self, context, at, skip):
        result = self.matcher.match(context, at, None)
        if result:
            return Result(self.action, result, context.text, at, at)

    def __eq__(self, other):
        return type(other) == VerbatimMatcher and other.matcher == self.matcher

    def __hash__(self):
        return hash(self.matcher)

    def __str__(self):
        return "<<%s>>" % self.matcher

    def __repr__(self):
        return "VerbatimMatcher(%s)" % repr(self.matcher)


########################################################################################################################


class TestMatchers(unittest.TestCase):

    skip = RegexpMatcher(r'\s+')

    def test_string_matcher(self):
        matcher = StringMatcher('hello')
        self.assertIsNotNone(matcher.match(Context(None, "hello"), 0, self.skip))
        self.assertIsNotNone(matcher.match(Context(None, " \n\thello"), 0, self.skip))
        self.assertIsNone(matcher.match(Context(None, "Hello"), 0, self.skip))
        self.assertIsNone(matcher.match(Context(None, "hello"), 1, self.skip))
        self.assertIsNone(matcher.match(Context(None, "hello"), 9, self.skip))

    def test_regexp_matcher(self):
        matcher = RegexpMatcher(re.compile('hello', re.IGNORECASE))
        self.assertIsNotNone(matcher.match(Context(None, "hello"), 0, self.skip))
        self.assertIsNotNone(matcher.match(Context(None, " \n\thello"), 0, self.skip))
        self.assertIsNotNone(matcher.match(Context(None, "Hello"), 0, self.skip))
        self.assertIsNotNone(matcher.match(Context(None, "HELLO"), 0, self.skip))
        self.assertIsNone(matcher.match(Context(None, "hell"), 0, self.skip))
        self.assertIsNone(matcher.match(Context(None, "hello"), 1, self.skip))
        self.assertIsNone(matcher.match(Context(None, "hello"), 9, self.skip))

    def test_selection_matcher(self):
        matcher = SelectionMatcher(StringMatcher('hello'), StringMatcher('world'))
        self.assertIsNotNone(matcher.match(Context(None, "hello"), 0, self.skip))
        self.assertIsNotNone(matcher.match(Context(None, "world"), 0, self.skip))
        self.assertIsNone(matcher.match(Context(None, ""), 0, self.skip))

    def test_sequence_matcher(self):
        matcher = SequenceMatcher(StringMatcher('hello'), StringMatcher('world'))
        self.assertIsNotNone(matcher.match(Context(None, "hello world"), 0, self.skip))
        self.assertIsNone(matcher.match(Context(None, "hello"), 0, self.skip))
        self.assertIsNone(matcher.match(Context(None, "world"), 0, self.skip))

    def test_repeat_matcher(self):
        matcher = RepeatMatcher(2, 5, StringMatcher('a'))
        self.assertIsNone(matcher.match(Context(None, ""), 0, self.skip))
        self.assertIsNone(matcher.match(Context(None, "a"), 0, self.skip))
        self.assertIsNotNone(matcher.match(Context(None, "aa"), 0, self.skip))
        self.assertIsNotNone(matcher.match(Context(None, "aaa"), 0, self.skip))
        self.assertIsNotNone(matcher.match(Context(None, "aaaa"), 0, self.skip))
        self.assertIsNotNone(matcher.match(Context(None, "aaaaa"), 0, self.skip))
        self.assertIsNone(matcher.match(Context(None, "aaaaaa"), 0, self.skip))
        self.assertIsNotNone(matcher.match(Context(None, "aaaaaaa"), 2, self.skip))

    def test_reference_matcher(self):
        matchers = {'word': RegexpMatcher(re.compile(r'\w+'))}
        matcher = ReferenceMatcher('word')
        self.assertIsNotNone(matcher.match(Context(matchers, "hello"), 0, self.skip))
        self.assertIsNone(matcher.match(Context(matchers, "..."), 0, self.skip))
        matchers = {}
        self.assertIsNone(matcher.match(Context(matchers, "hello"), 0, self.skip))

    def test_lookahead_matcher(self):
        matcher = LookaheadMatcher(StringMatcher('hello'))
        result = matcher.match(Context(None, "hello"), 0, self.skip)
        self.assertIsNotNone(result)
        self.assertEqual(result.end, 0)
        self.assertIsNone(matcher.match(Context(None, "world"), 0, self.skip))
        extended_matcher = SequenceMatcher(matcher, StringMatcher('hello world'))
        self.assertIsNotNone(extended_matcher.match(Context(None, "hello world"), 0, self.skip))
        self.assertIsNone(extended_matcher.match(Context(None, "hello, world"), 0, self.skip))

    def test_not_matcher(self):
        matcher = NotMatcher(StringMatcher('world'))
        result = matcher.match(Context(None, "hello"), 0, self.skip)
        self.assertIsNotNone(result)
        self.assertEqual(result.end, 0)
        self.assertIsNone(matcher.match(Context(None, "world"), 0, self.skip))

    def test_verbatim_matcher(self):
        matcher = StringMatcher('hello')
        self.assertIsNotNone(VerbatimMatcher(matcher).match(Context(None, "hello"), 0, self.skip))
        self.assertIsNotNone(matcher.match(Context(None, " hello"), 0, self.skip))
        self.assertIsNone(VerbatimMatcher(matcher).match(Context(None, " hello"), 0, self.skip))


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
                         ReferenceMatcher('x'))

    def test_sequence_word_rule(self):
        grammar = GrammarParser()
        self.assertEqual(grammar.parse("hello", goal='sequence_word'),
                         ReferenceMatcher('hello'))
        self.assertEqual(grammar.parse("!hello", goal='sequence_word'),
                         NotMatcher(ReferenceMatcher('hello')))
        self.assertEqual(grammar.parse("hello?", goal='sequence_word'),
                         RepeatMatcher(0, 1, ReferenceMatcher('hello')))
        self.assertEqual(grammar.parse("hello*", goal='sequence_word'),
                         RepeatMatcher(0, None, ReferenceMatcher('hello')))
        self.assertEqual(grammar.parse("hello+", goal='sequence_word'),
                         RepeatMatcher(1, None, ReferenceMatcher('hello')))
        self.assertEqual(grammar.parse("hello<3>", goal='sequence_word'),
                         RepeatMatcher(3, 3, ReferenceMatcher('hello')))
        self.assertEqual(grammar.parse("hello<,3>", goal='sequence_word'),
                         RepeatMatcher(0, 3, ReferenceMatcher('hello')))
        self.assertEqual(grammar.parse("hello<3,>", goal='sequence_word'),
                         RepeatMatcher(3, None, ReferenceMatcher('hello')))
        self.assertEqual(grammar.parse("hello<,>", goal='sequence_word'),
                         RepeatMatcher(0, None, ReferenceMatcher('hello')))
        self.assertEqual(grammar.parse("hello<5,7>", goal='sequence_word'),
                         RepeatMatcher(5, 7, ReferenceMatcher('hello')))
        # ...


class TestGrammar(unittest.TestCase):

    class HelloGrammar(Grammar):

        def statement_rule(self):
            r"statement = 'hello' r'\s+' 'world'"

        # ...

    def test_simple_grammar(self):
        grammar = self.HelloGrammar()
        self.assertIsNotNone(grammar.parse("statement", "hello world"))
        # ...
