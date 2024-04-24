Put all three files in the Mathlib folder in a project.
Run change.py on deligne.lean specifying the deligne.lean path in your Mathlib directory.
The output of change.py will be a set of imports required for the deligne.lean file.
Copy this set of imports and paste it into the getdefs.py file.
Run getdefs.py and the output will be a new file for each import file
containing the definitions and structures together with the name of the
original import file.
