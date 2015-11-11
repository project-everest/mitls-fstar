#!/usr/bin/env python

from __future__ import print_function
import sys

def main():
	fs = open(sys.argv[1]).read().splitlines()
	fs = map(lambda f: {'name':f, 'contents':open(f).readlines()},fs)
	for f in fs:
		buffer = ''
		multiline = 0
		is_first = True
		for i,line in enumerate(f['contents'],start=1):
			multiline += line.count('(*')
			if (line.count('//') > 0 or multiline > 0) and not is_first:
				buffer += '{}: {}'.format(i,line)
			closed = line.count('*)')
			if closed > 0 and is_first:
				is_first = False
			multiline -= closed
		if buffer:
			print ('*** {}:'.format(f['name']))
			print (buffer)
			print ()

if __name__ == '__main__':
	main()
