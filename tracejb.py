# tracing the poor man's way
# yes I know it is UGLY
# but it allows me to trace what the to_VDHL() conversion is doing
# and, when it bombs-out I have some clues where it happened


from __future__ import absolute_import
from __future__ import print_function

# import sys
# import inspect


tracejbindentlevel = 0
previous = False
DEBUGINDENT = 2


class Tracing(object):

    def __init__(self, initialstate=False, message=None, source=None):
        self._level = 0
        self._trace = initialstate
        self._message = message if message is not None else ''
        self._source = source
        self._tracestack = []

    def push(self, newstate=None, message=None):
        self._tracestack.append([self._trace, self._message])
        if newstate is not None:
            self._trace = bool(newstate)
        self._message += (' ' + message) if message is not None else ''
        self._level += 2

    def pop(self):
        if self._level > 0:
            self._trace, self._message = self._tracestack.pop()
            self._level -= 2

    def print(self, *args):
        if self._trace:
            if self._source is None:
                print('{}  '.format(self._message), end='')
            else:
                print('[{} {}]  '.format(self._source, self._message), end='')
            print(*args)


# filetracejb = open("Tracejb.log", 'w')
#
# nodetrace = ''
# def tracenode( name = None, op = 'add'):
#     global nodetrace
#
#     if name is None:
#         # step back one 'name'
#         nodetrace, _, _ = nodetrace.rpartition('.')
#         print >> filetracejb, '({})'.format(nodetrace)
#
#     elif isinstance(name, str):
#         if op == 'add':
#             nodetrace += '.' + name
#         else:
#             # 'restart'
#             nodetrace = name
#         print >> filetracejb, nodetrace
#
# def tracejb( name , info = None):
#     ''' increase the indent and print '''
#     global tracejbindentlevel
#     tracejbindentlevel += DEBUGINDENT
#
#     # make the indent
#     r = "%*s" % ( tracejbindentlevel, ' ')
#     # possibly prefix the info
#     if not info is None:
#         r += "%s: " % info
#     # the variable
#     r += "%s" % name
#     # print it
#     print >> filetracejb, r
#
# def tracejbdedent():
#     ''' decrease the indent by one step '''
#     global tracejbindentlevel
#     if tracejbindentlevel >= DEBUGINDENT :
#         tracejbindentlevel -= DEBUGINDENT
#
#
# def logjb( s = None , info = None , sameline = False ):
#     ''' print additional info, indented by one extra space
#         conditionally ending the line, so we can print multiple things
#         on the same line, easying a bit on  the reading
#         '''
#     global tracejbindentlevel
#     global previous
#
#     if s is not None or info is not None:
#         if sameline and not previous:
#             previous = True
#             if info is None:
#                 print >> filetracejb, "s%*s%s" % ( tracejbindentlevel+1, ' ', s) ,
#             else:
#                 print >> filetracejb, "%*s%s: %s" % ( tracejbindentlevel+1, ' ', info, s) ,
#         else:
#             if previous:
#                 previous = sameline
#                 if info is None:
#                     print >> filetracejb, ", %s" % ( s),
#                 else:
#                     print >> filetracejb, ", %s: %s" % (info, s),
#                 if not sameline:
#                     print >> filetracejb
#             else:
#                 if info is None:
#                     print >> filetracejb, "%*s%s" % (  tracejbindentlevel+1, ' ', s)
#                 else:
#                     print >> filetracejb, "%*s%s: %s" % ( tracejbindentlevel+1, ' ', info, s)
#     else:
#         # single return
#         print >> filetracejb
#
#
# def logjbwr( s ):
#     ''' simply print starting at the full left '''
#     print >> filetracejb, "%s" % s
#
#
# def logjbinspect( obj , info = None, doinspect = True):
#     if info is None:
#         print >> filetracejb, "%*s%s" % (  tracejbindentlevel+1, ' ', obj)
#     else:
#         print >> filetracejb, "%*s%s: %s" % ( tracejbindentlevel+1, ' ', info, obj)
#
#     if doinspect:
#         for item in inspect.getmembers( obj):
#             if not item[0].startswith('__') and not item[0].endswith('__') :
#                 logjb( item, ' '  )
#
#
