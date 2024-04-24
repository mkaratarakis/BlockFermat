1.Put all three files in the Mathlib folder in a project.

2.Run change.py on deligne.lean specifying the deligne.lean path in your Mathlib directory.

3.The output of change.py will be a set of imports required for the deligne.lean file.

4.Copy this set of imports and paste it into the getdefs.py file.

5.Run getdefs.py and the output will be a new file for each import file
containing the definitions and structures together with the name of the
original import file.
