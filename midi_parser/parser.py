#!/usr/bin/python

import sys
from mido import MidiFile

def parse (midifile) :
    mid = MidiFile(midifile)
    output = ""
    for i, track in enumerate(mid.tracks):
        output += ('Track {}: {}'.format(i, track.name)) + "\n"
        for msg in track:
            output += str(msg) + "\n"
    return output


if len(sys.argv) == 1:
    print('Missing argument!')
elif len(sys.argv) == 2:
    print(parse(sys.argv[1]))
else:
    print('Too many arguments!')
