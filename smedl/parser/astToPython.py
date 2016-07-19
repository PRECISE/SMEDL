from grako.ast import AST

class AstToPython(object):

    @classmethod
    def expr(cls, object):
        if isinstance(object, AST):
            for k, v in list(object.items()):
                if k == 'or_ex':
                    ored = [cls.expr(val) for val in v]
                    return "(" + " || ".join(ored) + ")"
                elif k == 'and_ex':
                    anded = [cls.expr(val) for val in v]
                    return "(" + " && ".join(anded) + ")"
                elif k == 'not_ex':
                    return "!(%s)" % cls.expr(v)
                elif k == 'comp':
                    comps = []
                    for val in v:
                        arith = val.get('arith')
                        if arith:
                            operators = val.get('operator')
                            result = cls.arith(arith, operators)
                            comps.append(" ".join(result))
                        else:
                            comps.append(cls.term(val))
                    return (" %s " % object['operator']).join(comps)
                elif k == 'index':
                    return "[%s]" % cls.expr(v)
                elif k == 'params':
                    if isinstance(v, list):
                        return "(%s)" % (", ".join([cls.expr(val) for val in v]))
                    else:
                        return "(%s)" % cls.expr(v)
                elif k == 'dot':
                    trailer = ""
                    if object['trailer']:
                        trailer = cls.expr(object['trailer'])
                    return ".%s%s" % (v, trailer)
                elif k == 'arith':
                    operators = object.get('operator')
                    result = cls.arith(v, operators)
                    return " ".join(result)
                else:
                    return cls.term(object)
        elif object is "":
            return ""


    @classmethod
    def arith(cls, terms, operators):
        result = [None] * ( len(terms) + len(operators) )
        result[::2] = [ cls.term(term) for term in terms ]
        result[1::2] = operators
        return result


    @classmethod
    def term(cls, term):
        if isinstance(term, AST):
            if(term.get('arith')):
                return "(" + cls.expr(term) + ")"
            unary = term.get('unary') or ""
            if isinstance(unary, list):
                unary = "".join(unary)
            atom = term.get('atom') or ""
            term_text = "%s%s" % (unary, atom)
            if isinstance(term.get('trailer'), AST):
                for k, v in list(term.items()):
                    term_text = "%s%s" % (term_text, cls.expr(v) or "")
            return term_text
        else:
            return ""


    @classmethod
    def expr_list(cls, inputlist):
        if inputlist[0] is not None and isinstance(inputlist[0], list):
            inputlist = inputlist[0]
        out = []
        for el in inputlist:
            if cls.expr(el) is not None:
                out.append(cls.expr(el))
        return out
