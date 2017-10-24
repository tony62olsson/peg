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
        result, end = ReferenceMatcher(goal).match(Context(self.rules, text), 0, RegexpMatcher(r'\s*'))
        if result is not None and end == len(text):
            return Matcher.apply(result, self)
        else:
            return None

    def _statement_matcher(self):
        # statement = word '=' rule
        return SequenceMatcher(self.name, StringMatcher('='), ref('rule'))

    def statement_rule(self, rule):
        return rule[0].group(0), rule[2]

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
        m1 = rep0(StringMatcher('/'), ref('sequence'))
        return SequenceMatcher(m0, m1)

    def rule_visitor(self, rule):
        m0, m1 = rule
        if m1:
            return SelectionMatcher(m0, *list(sequence for _, sequence in m1))
        else:
            return m0

    def _sequence_matcher(self):
        # sequence = {sequence_word} ['&' {sequence_word}+]
        m0 = rep0(ref('sequence_word'))
        m1 = opt(StringMatcher('&'), rep1(ref('sequence_word')))
        return SequenceMatcher(m0, m1)

    def sequence_visitor(self, rule):
        m0, m1 = rule
        if len(m0) == 1:
            result = m0[0]
        else:
            result = SequenceMatcher(*m0)
        return result

    def _sequence_word_matcher(self):
        # sequence_word = ['!'] word ['?' | '*' | '+' | '<' times '>' | '<' [lower] ',' [upper] '>'
        m0 = opt(StringMatcher('!'))
        m1 = ref('word')
        m2 = opt(SelectionMatcher(StringMatcher('?'),
                                  StringMatcher('*'),
                                  StringMatcher('+'),
                                  SequenceMatcher(StringMatcher('<'), self.number, StringMatcher('>')),
                                  SequenceMatcher(StringMatcher('<'), opt(self.number), StringMatcher(','), opt(self.number), StringMatcher('>'))))
        return SequenceMatcher(m0, m1, m2)

    def sequence_word_visitor(self, rule):
        m0, m1, m2 = rule
        if m2:
            repeat_val = m2[0]
            if type(repeat_val) == tuple:
                repeat_str = repeat_val[0]
                if repeat_str == '?':
                    m1 = RepeatMatcher(0, 1, m1)
                elif repeat_str == '*':
                    m1 = RepeatMatcher(0, None, m1)
                elif repeat_str == '+':
                    m1 = RepeatMatcher(1, None, m1)
            elif len(repeat_val) == 3:
                m1 = RepeatMatcher(repeat_val[1], repeat_val[1], m1)
            else:
                lower_opt = repeat_val[1]
                upper_opt = repeat_val[3]
                lower = lower_opt[0] if lower_opt else 0
                upper = upper_opt[0] if upper_opt else None
                m1 = RepeatMatcher(lower, upper, m1)
        if m0:
            m1 = NotMatcher(m1)
        return m1

    def _word_matcher(self):
        # word = regexp / string / name / '(' rule ')' / '{' rule '}' / '[' rule ']' / '<<' rule '>>
        return SelectionMatcher(self.regexp,
                                self.string,
                                NamedMatcher('reference', self.name),
                                NamedMatcher('group', SequenceMatcher(StringMatcher('('), ref('rule'), StringMatcher(')'))),
                                NamedMatcher('repeat', SequenceMatcher(StringMatcher('{'), ref('rule'), StringMatcher('}'))),
                                NamedMatcher('optional', SequenceMatcher(StringMatcher('['), ref('rule'), StringMatcher(']'))),
                                NamedMatcher('verbatim', SequenceMatcher(StringMatcher('<<'), ref('rule'), StringMatcher('>>'))))

    def word_visitor(self, word):
        return word

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

    def _name_matcher(self):
        return RegexpMatcher(r'\w+')

    def _string_matcher(self):
        return NamedMatcher('string', RegexpMatcher(r"'(?:\\'|[^'])*'"))

    def string_visitor(self, value):
        return StringMatcher(ast.literal_eval(value.group(0)))

    def _regexp_matcher(self):
        return NamedMatcher('regexp', RegexpMatcher(r"r'(?:\\'|[^'])*'"))

    def regexp_visitor(self, value):
        return RegexpMatcher(ast.literal_eval(value.group(0)))

    def _number_matcher(self):
        return NamedMatcher('number', RegexpMatcher(r'\d+'))

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


class Result(object):

    # Result node should only be created by a ReferenceMatcher, StringMatcher and RegexpMatcher all other collapse
    # to items or lists

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

    @staticmethod
    def _skip(context, at, skip):
        if skip:
            result, end = skip.match(context, at, None)
            while result and end > at:
                at = end
                result, end = skip.match(context, at, None)
        return at

    @classmethod
    def apply(cls, match, visitor):
        if type(match) == list:
            return list(cls.apply(item, visitor) for item in match)
        elif type(match) == tuple and not type(match[1]) == int:
            return cls.visit(visitor, match[0], cls.apply(match[1], visitor))
        else:
            return match

    @classmethod
    def visit(cls, visitor, name, args):
        for suffix in ['_visitor', '_rule']:
            fn_name = name + suffix
            if fn_name in visitor.__class__.__dict__:
                return visitor.__class__.__dict__[fn_name](visitor, args)
        raise Exception("%s.%s do not have a '%s_visitor' or '%s_rule' method defined" %
                        (visitor.__class__.__module__, visitor.__class__.__name__, name, name))


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
