#!/usr/bin/python

import sys
import mido
from music21 import pitch

def bremen_pitch_string(midi_num):
  m21pitch = pitch.Pitch(midi_num)
  pitchclass = m21pitch.name
  modifierstr = m21pitch.accidental.name
  modifier = 0
  if modifierstr == "sharp": modifier = 1
  if modifierstr == "flat" : modifier = -1
  octave = m21pitch.octave
  brpitch = pitchclass[0] + ' # ' + str(modifier) + ' \' ' + str(octave)
  return brpitch

def bremen_duration_string(num, unit):
  durstr = unit
  for i in range(num-1):
    durstr = 'tie (' + durstr + ') (' + unit + ')'
  return durstr

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
          note = bremen_pitch_string(msgdict.get('note'))
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
    
    #legkisebb egység
    min_delta = 999999
    for i in notes:
      if i[1] != 0 and i[1] < min_delta: min_delta = i[1]
  
    # INNENTŐL FELTESZEM, HOGY A min_delta 2-ES LEOSZTÁSÚ HANGOT TALÁLT
    #hanghosszúság arányok számítása
       
    bremen_notes = [] 
    for i in notes:
      i[1] = bremen_duration_string(round((i[1] / min_delta)*2), 'Quarter_')
      if i[0] == 'rest':
        bremen_notes.append('rest_of (' + i[1] + ') (mf)')
      else:
        bremen_notes.append('note_of (' + i[0] + ') (' + i[1] + ') (mf)')

    melodic_part = ""
    bremen_notes.reverse()
    output = '(melodic_part_of ( '+ bremen_notes[0] + ' ))'
    for i in bremen_notes[1:]:
      output = '(longer ( ' + i + ')\n' + output + ')'
      
    coq_header = \
"""Require Import ZArith.
From Bremen.theories.harmony Require Import Letter PitchClass Pitch Chord Key Note.
From Bremen.theories.rhythm Require Import Duration Division.
From Bremen.theories.physics Require Import Dynamics.
From Bremen.theories.structure Require Import MelodicPart.

Definition melody1 :=
"""
  return coq_header + output + '.'


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
