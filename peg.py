import ast
import unittest
import abc
import re


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


class Grammar(object):
    """
Grammar:

* statement = name '=' rule
* rule = sequence {'/' sequence}
* sequence = {sequence_word} ['&' {sequence_word}+]
* sequence_word =  ['.'] ['!'] word ['?' / '*' / '+' / '<' [lower] [',' [upper]] '>']
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
* .             is no skip
"""

    def __init__(self):
        self.rules = dict()
        grammar_parser = GrammarParser()
        for name, func in self.__class__.__dict__.items():
            if name.startswith('rule_') or name.endswith('_rule'):
                name, rule = grammar_parser.parse(func.__doc__)
                self.rules.setdefault(name, RuleSelection()).add(rule)

    def parse(self, goal, text):
        return self.rules.setdefault(goal, RuleSelection()).match(Context(self, text), 0)


class GrammarParser(object):

    def __init__(self):
        WS = RuleRegexp(re.compile(r'\s*'))
        WORD = RuleRegexp(re.compile(r'\w+'), action=lambda r: r.group(0))
        STRING = RuleRegexp(re.compile(r"'(?:\\'|[^'])*'"), action=lambda r: RuleString(ast.literal_eval(r.group(0))))
        REGEXP = RuleRegexp(re.compile(r"r'(?:\\'|[^'])*'"), action=lambda r: RuleRegexp(re.compile(ast.literal_eval(r.group(0)))))
        NUMBER = RuleRegexp(re.compile('\d+'), action=lambda r: RuleRegexp(re.compile(ast.literal_eval(r.group(0)))))

        self.statement = RuleSelection(
            RuleSequence(WORD, WS, RuleString('='),
                         RuleRepeat(0, 10, RuleSequence(WS, RuleSelection(REGEXP, STRING, WORD),
                                                        action=lambda r: r[1].apply()),
                                    action=lambda r: RuleSequence(*list(r0.apply() for r0 in r))),
                         action=lambda r: (str(r[0]), r[3].apply()))
        )

        self.rules = {
            'statement':
                RuleSequence(WS, WORD, WS, RuleString('='), RuleReference('rule'), WS,
                             action=lambda r: (r[1].apply(), r[4].apply())),
            'rule':
                RuleSequence(RuleReference('sequence'),
                             RuleRepeat(0, None,
                                        RuleSequence(WS, RuleString('/'), RuleReference('sequence'),
                                                     action=lambda r: r[2].apply())),
                             action=lambda r: ((lambda r0, r1: RuleSelection(r0, *r1) if r1 else r0)(r[0].apply(), r[1].apply()))),
            'sequence':
                RuleSequence(RuleRepeat(0, None, RuleReference('sequence_word')),
                             RuleRepeat(0, 1, RuleSequence(WS, RuleString('&'),
                                                           RuleRepeat(1, None, RuleReference('sequence_word')))),
                             action=lambda r: RuleSequence(*r[0].apply())),
            'sequence_word':
                RuleSequence(RuleRepeat(0, 1, RuleSequence(WS, RuleString('.'))),
                             RuleRepeat(0, 1, RuleSequence(WS, RuleString('!'))),
                             RuleReference('word'),
                             RuleRepeat(0, 1, RuleSequence(WS, RuleSelection(
                                 RuleString('?', action=lambda _: (0, 1)),
                                 RuleString('*', action=lambda _: (0, None)),
                                 RuleString('+', action=lambda _: (0, None)),
                                 RuleSequence(RuleString('<'), RuleSelection(
                                     RuleSequence(WS, RuleRepeat(0, 1, NUMBER, action=lambda r: r[0] if r else 0),
                                                  WS, RuleString(','),
                                                  WS, RuleRepeat(0, 1, NUMBER, action=lambda r: r[0] if r else None),
                                                  action=lambda r: (r[1], r[5])),
                                     RuleSequence(WS, NUMBER, action=lambda r: (r[1], r[1]))),
                                              WS, RuleString('>'),
                                              action=lambda r: r[1])),
                                                           action=lambda r: r[1])),
                             action=lambda r: r[2].result.apply()),
            'word':
                RuleSelection(RuleSequence(WS, REGEXP, action=lambda r: r[1].apply()),
                              RuleSequence(WS, STRING, action=lambda r: r[1].apply()),
                              RuleSequence(WS, WORD, action=lambda r: RuleReference(r[1].apply())),
                              RuleSequence(WS, RuleString('('), RuleReference('rule'), WS, RuleString(')'), action=lambda r: r[2].apply()),
                              RuleSequence(WS, RuleString('{'), RuleReference('rule'), WS, RuleString('}'), action=lambda r: r[2].apply()),
                              RuleSequence(WS, RuleString('['), RuleReference('rule'), WS, RuleString(']'), action=lambda r: r[2].apply()),
                              RuleSequence(WS, RuleString('<<'), RuleReference('rule'), WS, RuleString('>>'), action=lambda r: r[2].apply()))

        }

    @trace
    def parse(self, text, goal='statement'):
        match = self.rules[goal].match(Context(self.rules, text), 0)
        if match:
            return match.apply()


class Context(object):

    def __init__(self, rules, text):
        self.rules = rules
        self.text = text

    def __repr__(self):
        return "Context(%s)" % repr(self.text)


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


class Rule(object):

    WORD = re.compile(r''''(?:\\'|[^'])*'|\S+''')

    @classmethod
    def make(cls, text):
        words = cls.WORD.findall(text)
        return RuleSequence(list(RuleString(word) for word in words))

    @abc.abstractmethod
    def match(self, context, at):
        raise NotImplemented()


class RuleString(Rule):

    def __init__(self, word, action=None):
        self.action = action
        self.word = word
        self.length = len(word)

    @memoize
    def match(self, context, at):
        if context.text.startswith(self.word, at):
            return Result(self.action, self.word, context.text, at, at + self.length)

    def __str__(self):
        return repr(self.word)

    def __repr__(self):
        return "RuleString(%s)" % repr(self.word)


class RuleRegexp(Rule):

    def __init__(self, regexp, action=None):
        self.action = action
        self.regexp = regexp

    @memoize
    def match(self, context, at):
        match = self.regexp.match(context.text, at)
        if match:
            return Result(self.action, match, context.text, at, match.end(0))
        else:
            return None

    def __str__(self):
        return 'r' + repr(self.regexp.pattern)

    def __repr__(self):
        return "RuleRegexp(%s)" % repr(self.regexp.pattern)


class RuleSequence(Rule):

    def __init__(self, *rules, action=None):
        self.action = action
        self.rules = list(rules)

    def add(self, rule):
        self.rules.append(rule)

    @memoize
    def match(self, context, at):
        sequence = list()
        end = at
        for rule in self.rules:
            result = rule.match(context, end)
            if result is None:
                return None
            end = result.end
            sequence.append(result)
        return Result(self.action, sequence, context.text, at, end)

    def __str__(self):
        return "(%s)" % ' '.join(str(r) for r in self.rules)

    def __repr__(self):
        return "RuleSequence(%s)" % ', '.join(repr(r) for r in self.rules)


class RuleSelection(Rule):

    def __init__(self, *rules, action=None):
        self.action = action
        self.rules = list(rules)

    def add(self, rule):
        self.rules.append(rule)

    @memoize
    def match(self, context, at):
        for rule in self.rules:
            result = rule.match(context, at)
            if result is not None:
                return Result(self.action, result, context.text, at, result.end)
        return None

    def __str__(self):
        return ' / '.join(str(r) for r in self.rules)

    def __repr__(self):
        return "RuleSelection(%s)" % ', '.join(repr(r) for r in self.rules)


class RuleRepeat(Rule):

    def __init__(self, lower, upper, rule, action=None):
        self.action = action
        self.lower = lower
        self.upper = upper
        self.rule = rule

    @memoize
    def match(self, context, at):
        end = at
        sequence = list()
        count = 0
        result = self.rule.match(context, end)
        while result:
            end = result.end
            if count == self.upper:
                return None
            sequence.append(result)
            count += 1
            result = self.rule.match(context, end)
        if count < self.lower:
            return None
        return Result(self.action, sequence, context.text, at, end)

    def __str__(self):
        if self.lower == 0 and self.upper is None:
            return "{%s}" % self.rule
        elif self.lower == 0 and self.upper == 1:
            return "[%s]" % self.rule
        elif self.lower == 0:
            return "{%s}<,%d>" % (self.rule, self.upper)
        elif self.upper is None:
            return "{%s}<%d,>" % (self.rule, self.lower)
        else:
            return "{%s}<%d,%d>" % (self.rule, self.lower, self.upper)

    def __repr__(self):
        return "RuleSelection(%s, %s, %s)" % (self.lower, self.upper, repr(self.rule))


class RuleReference(Rule):

    def __init__(self, name, action=None):
        self.action = action
        self.name = name

    def match(self, context, at):
        if self.name in context.rules:
            result = context.rules[self.name].match(context, at)
            if result:
                return Result(self.action, result, context.text, at, result.end)

    def __eq__(self, other):
        return type(other) == RuleReference and other.name == self.name

    def __str__(self):
        return self.name

    def __repr__(self):
        return "RuleReference(%s)" % self.name


class TestRule(unittest.TestCase):

    WS = re.compile(r'\s+')

    def test_string_rule(self):
        rule = RuleString('hello')
        self.assertIsNotNone(rule.match(Context(None, "hello"), 0))
        self.assertIsNone(rule.match(Context(None, "Hello"), 0))
        self.assertIsNone(rule.match(Context(None, "hello"), 1))
        self.assertIsNone(rule.match(Context(None, "hello"), 9))

    def test_regexp_rule(self):
        rule = RuleRegexp(re.compile('hello', re.IGNORECASE))
        self.assertIsNotNone(rule.match(Context(None, "hello"), 0))
        self.assertIsNotNone(rule.match(Context(None, "Hello"), 0))
        self.assertIsNotNone(rule.match(Context(None, "HELLO"), 0))
        self.assertIsNone(rule.match(Context(None, "hell"), 0))
        self.assertIsNone(rule.match(Context(None, "hello"), 1))
        self.assertIsNone(rule.match(Context(None, "hello"), 9))

    def test_selection_rule(self):
        rule = RuleSelection(RuleString('hello'), RuleRegexp(self.WS), RuleString('world'))
        self.assertIsNotNone(rule.match(Context(None, "hello"), 0))
        self.assertIsNotNone(rule.match(Context(None, "   "), 0))
        self.assertIsNotNone(rule.match(Context(None, "world"), 0))
        self.assertIsNone(rule.match(Context(None, ""), 0))

    def test_sequence_rule(self):
        rule = RuleSequence(RuleString('hello'), RuleRegexp(self.WS), RuleString('world'))
        self.assertIsNotNone(rule.match(Context(None, "hello world"), 0))
        self.assertIsNone(rule.match(Context(None, "hello"), 0))
        self.assertIsNone(rule.match(Context(None, "    "), 0))
        self.assertIsNone(rule.match(Context(None, "world"), 0))

    def test_repeat_rule(self):
        rule = RuleRepeat(2, 5, RuleString('a'))
        self.assertIsNone(rule.match(Context(None, ""), 0))
        self.assertIsNone(rule.match(Context(None, "a"), 0))
        self.assertIsNotNone(rule.match(Context(None, "aa"), 0))
        self.assertIsNotNone(rule.match(Context(None, "aaa"), 0))
        self.assertIsNotNone(rule.match(Context(None, "aaaa"), 0))
        self.assertIsNotNone(rule.match(Context(None, "aaaaa"), 0))
        self.assertIsNone(rule.match(Context(None, "aaaaaa"), 0))
        self.assertIsNotNone(rule.match(Context(None, "aaaaaaa"), 2))

    def test_reference_rule(self):
        rules = {'ws': RuleRegexp(re.compile(r'\s+')),
                 'word': RuleRegexp(re.compile(r'\w+'))}
        rule = RuleRepeat(0, None, RuleSelection(RuleReference('ws'), RuleReference('word')))
        self.assertIsNotNone(rule.match(Context(rules, ""), 0))
        self.assertIsNotNone(rule.match(Context(rules, "hello"), 0))
        self.assertIsNotNone(rule.match(Context(rules, "hello world"), 0))


class TestGrammarParser(unittest.TestCase):

    def test_word_rule(self):
        grammar = GrammarParser()
        self.assertEqual(grammar.parse("hello", goal='word'), RuleReference('hello'))
        self.assertIsNotNone(grammar.parse("'hello world'", goal='word'))
        self.assertIsNotNone(grammar.parse("r'hello\s+world'", goal='word'))
        self.assertIsNotNone(grammar.parse("(ws)", goal='word'))
        self.assertIsNotNone(grammar.parse("{ws ws}", goal='word'))
        self.assertIsNotNone(grammar.parse("[ws / ws]", goal='word'))

    def test_sequence_word_rule(self):
        grammar = GrammarParser()
        self.assertIsNotNone(grammar.parse("hello", goal='sequence_word'))


class TestGrammar(unittest.TestCase):

    class HelloGrammar(Grammar):

        def statement_rule(self):
            r"statement = 'hello' r'\s+' 'world'"

        def ws_rule(self):
            r"ws = r'\s+'"

    def test_simple_grammar(self):
        grammar = self.HelloGrammar()
        self.assertIsNotNone(grammar.parse("statement", "hello world"))
