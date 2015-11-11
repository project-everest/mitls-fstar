#! /usr/bin/env python

# --------------------------------------------------------------------
import sys, os, re, locale, subprocess as sp

# --------------------------------------------------------------------
def _get_certificates(store):
    def _info_from_line(line):
        m = re.match(r'^\s+Subject Name: (.*)', line)
        if m is not None:
            data = re.split(',\s*', m.group(1))
            data = [x for x in data if '=' in x]
            data = dict([x.split('=', 1) for x in data])
            if 'CN' in data:
                return ('cn', unicode(data['CN'], 'utf-8'))
            return None

        m = re.match(r'^\s+Unique Hash:\s*(\w+)', line)
        if m is not None:
            return ('hash', m.group(1))

        return None

    command = ['certmgr', '-list', '-c', store]
    output  = sp.Popen(command, stdout = sp.PIPE).communicate()[0]
    crts    = []
    crtsmap = dict()
    ctxt0   = dict(cn = None, hash = None)
    ctxt    = ctxt0.copy()

    def _valid_ctxt(ctxt):
        return ctxt['cn'] != None and ctxt['hash'] != None

    for line in output.splitlines():
        if re.search('^(Self-signed)?\s*X.509', line):
            if _valid_ctxt(ctxt):
                crts.append(ctxt)
            ctxt = ctxt0.copy()
            continue

        info = _info_from_line(line)
        if info is not None:
            ctxt[info[0]] = info[1]

    if _valid_ctxt(ctxt):
        crts.append(ctxt)

    for x in crts:
        crtsmap.setdefault(x['cn'], []).append(x['hash'])

    return crtsmap

# --------------------------------------------------------------------
def _main():
    locale.setlocale(locale.LC_ALL, 'C')

    trcrts = _get_certificates('Trust')
    mycrts = _get_certificates('My')
    hashes = set()

    for cn in sys.argv[1:]:
        for crts in (trcrts, mycrts):
            for h in crts.get(cn, []):
                hashes.add(h)
    for h in hashes:
        print h

# --------------------------------------------------------------------
if __name__ == '__main__':
    _main()
