# Feladat 1
# ---------
# Nagy adag adott hangfájl feldolgozását követően különítsük el a zenét
# tartalmazóak közül azokat, amelyeken végig csak egy trombita játszik, a
# teljes dal a C2 - Cb4 hangtartományon belül van és nem szerepel benne tritónusz
# lépés.

sampling_rate = 5
so1 = [{440.0: 10.0, 880: 9.0},
       {440.0: 10.0, 880: 9.0}]
so2 = [{440.0: 10.0, 880: 9.0},
       {440.0: 10.0, 880: 9.0}]
so3 = [{440.0: 10.0, 880: 9.0},
       {440.0: 10.0, 880: 9.0}]
sounding_objects = [so1, so2, so3]

criteria = """
Definition criteria (so : sounding_object) : bool :=
  andb (maximum_one_pitch_with_instrument so trumpet)
  (lowest_frequency_within so (from_pitch C2) (from_pitch Cb4)).
"""

def parse_sounding_object_to_bremen (sounding_object) :
    bremen_str = """(* THIS IS A GENERATED FILE *)
From Bremen.theories.physics Require Import FrequencySample Frequency Instrument SoundingObject.
From Bremen.theories.harmony Require Import Pitch.
Require Import QArith PArith List.
Import ListNotations.

Definition so1 : sounding_object := sounding_obj
    """
    bremen_str += str(sampling_rate) + "%N ["

    for sample in sounding_object:
        bremen_str +="["
        for freq in sample:
            bremen_str += f'({freq} Hz {sample.get(freq)} dB);'
        bremen_str = bremen_str[:-1]
        bremen_str +="];"
    bremen_str = bremen_str[:-1]
    bremen_str += "]."

    bremen_str += "\n" + criteria + "Eval compute in criteria so1."
    return bremen_str

def compile_bremen_source_files (dir) :
    print(1)

def main () :
    # Saving bremen source files
    file_count = 1
    for so in sounding_objects:
        f = open(f'so{file_count}.v', "w")
        f.write(parse_sounding_object_to_bremen(so))
        f.close()
        file_count += 1

main()

# Feladat 2
# ---------
# Az elkülönített hang objektumoknak készítsük el a leiratát és a feltehetően
# megfelelőek közül vegyük azokat, amelyek csak a F# dúr hármashangzat
# hangjait tartalmazzák.
