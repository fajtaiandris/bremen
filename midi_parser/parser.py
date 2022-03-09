#!/usr/bin/python

import sys
import mido
from music21 import pitch

def parse (midifile) :
  mid = mido.MidiFile(midifile)
  preparsed_midi = []
  if len(mid.tracks) != 1:
    raise Exception("Multitrack input is not supported!")
  else:
    for i, track in enumerate(mid.tracks):
      for msg in track:
        msgdict = msg.dict()
        if msgdict.get('type') == 'note_on':
          note = str(pitch.Pitch(msgdict.get('note')))
          event = 'start' if msgdict.get('velocity') != 0 else 'stop'
          deltasec = msgdict.get('time')
          preparsed_midi.append([event, note, deltasec])

    parsed_midi = []
    next_is_start = True
    legato_ratio = 0.1
    
    for i in range(len(preparsed_midi)):
      current = preparsed_midi[i]
      if next_is_start and current[0] == 'stop':
        raise Exception("Polyphonic melody is not supported!")
      else:
        next_is_start = not next_is_start
        if i != 0:
          previous = preparsed_midi[i-1]
          #hangok közötti rövid szünetek összeolvasztása a korábbi hanggal
          if current[0] == 'start' and current[2] != 0:
            if current[2] < previous[2] * legato_ratio:
              previous[2] += current[2]
              current[2] = 0
            else:
            #szünetek megállapítása
              current[1] = 'rest'
              parsed_midi.append(current)
          else: 
            parsed_midi.append(current)

    #event címkék törlése
    notes = []
    for i in parsed_midi:
      notes.append([i[1], i[2]])
    
    #legkissebb egység
    min_delta = 999999
    for i in notes:
      if i[1] != 0 and i[1] < min_delta: min_delta = i[1]
  
    # INNENTŐL FELTESZEM, HOGY A min_delta 2-ES LEOSZTÁSÚ HANGOT TALÁLT
    #hanghosszúság arányok számítása
        
    for i in notes:
      i[1] = round((i[1] / min_delta)*2)
    
    
    output = ""
    for i in notes:
      output += i[0] + ' ' + str(i[1]) + '\n'
  return output


if len(sys.argv) == 1:
  print('Missing argument!')
elif len(sys.argv) == 2:
  print(parse(sys.argv[1]))
elif len(sys.argv) == 3:
  f = open(sys.argv[2], "w")
  f.write(parse(sys.argv[1]))
  f.close()
else:
  print('Too many arguments!')
