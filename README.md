#  CoqPIE

CoqPIE (an IDE for the Coq theorem prover + PEDANTIC)

SETTING UP THE EDITOR FOR YOUR PROJECT

To get started with CoqPIE, first make sure that you have Coq 8.4pl3 installed.
This is the only version of Coq for which the CoqPIE editor is known to work.
Many of the other version have slightly different output formats which the
editor is not able to handle.  Also, this version is only known to work on a
Mac running Python 2.7.10.

Start by trying out the three included sample projects.  Before you can use the
editor, you need to initialize the editor' cache.  Execute either the script
"buildSmall", "buildFoundations" or "buildPEDANTIC" to build the cache for one
of the three include projects.  For "buildSmall", the script takes about a
minute and for "buildPEDANTIC", the script takes about 15 minutes.  After the
script is done, a directory called prover.pp will appear which is the editor's
cache.  Also, the editor will come up.

If you exit the editor, you can bring it back up with the command

python project.py -p prover.pp

You can rename the "prover.pp" cache to any other name as long as the ".pp"
extension is preserved.

CREATING A SCRIPT FOR YOUR OWN PROJECT

Use either buildSmall or buildPEDANTIC as a model for creating a script to
initialize the editor for your own project.  Before creating your project,
first place all of the .v files for your project in a single directory.
Your build script is a single line command.  The command begins with
"python Project.py".  You will need to cd to the CoqPIE directory and place
the script in that directory.  After that you should have "--root=<dir>" where
<dir> is the relative path to the directory containing your .v files.
Following that is a list of all the .v files in the order in which they need
to be compiled.

USING THE EDITOR

After the editor comes up, you can select definitions in the tree at the left.
The middle window shows the source with the appropriate declaration
highlighted.  The window to the right shows the Coq output after the command
or proof step executed.  Since the entire project is pre-compiled and output
is captured, the Coq output after any step can be viewed by selecting different
commands.

EDITING THE SOURCE CODE

One can edit the source code in the middle window.  As definitions are altered,
they become yellow.  This indicates that the editor needs to reparse these
definitions.  To carry out the reparsing, press the "Parse" button in the
row of buttons above the middle window.  The project tree in the left window
is updated and definitions that need to be reverified with Coq become red or
yellow.

LOCATING A DECLARATION IN THE TREE

When a declaraction in the tree is selected, the source file is prompty moved
to the location of that definition.  Sometimes, it is useful to find the
position in the tree given the position of the cursor in the text.  To do this,
first move the cursor to the declaration or proof step.  Then press "TreeItem"
in the row of buttons above the middle window.

MANAGING THE COQTOP PROCESS

CoqPIE manages the coqtop process in a manner similar to that of either Proof
General or Coq IDE.  However, the process works over an entire project rather
than a single source file.  You can move the correct state of the coq process
to a particular declaration or proof step by first selecting the declaration
or proof step in the tree at the let and then pressing the "Selected" button in
the row of buttons above the middle window.  Definitions processed by Coq
change to grey.  A lighter shade is used to indicate progress of the Coq
process.  Since CoqPIE manages whole projects, if the definitions in the
current file depend on another file (which has been edited), that other file
is automatically recompiled.  There are also "Left" and "Right" buttons to
move up and down a single step in the Coq process.

FINDING A DECLARATION

Above the tree is a "find" box.  If you type the exact name of a declaration,
then that declaration will be highlighted in yellow.  Also, the file containing
the declaration will be highlighted in yellow.

OUTPUT WINDOW

The window on the right shows the Coq output after a proof step is executed.
Sometimes, CoqPIE can parse this output and present it in a formatted fashion.
For syntax/type checking errors in definitions, the erroneous text will be
marked in red.  For goal states after applying a proof tactic, the goals will
be shown with check boxes to the left.  Check the goals that you would like to
see expanded fully. Also, differences in hypotheses and goals from the previous
step are highlight.

There is a combo box above the window to select which differences to show.
The default choice is differences with the previous goal step.  Alternatively,
differences between hypotheses and the goal can be shown.  This is helpful when
choosing rewrites to transform goals.  Finally, one can show differences
between the current output and the last valid output which is used for replay
described in the next section.

There is also a check box titled "Show previous output".  This is for replay
described below.

REPLAY AND LEMMA EXTRACTION

Here are a couple of sample usages to illustrate how replay and lemma
extraction work.

Replay scenario:

    1) Start CoqPIE with:

       cd CoqPIE
       python project.py -p prover.pp
       (after doing ./buildSmall and closing the editor--there
        seems to be a bug when editing directly after the buildSmall)

    2) Select "../Small/Model.v" in the treeview window on the left.  Click the
       triangle to the left of the text to expand the entry.

    3) Edit the text to uncomment all commented constructs (in Exp, eval, pop,
       noFind, noRef and popEquiv)

    4) click the word "intros." on the fifth line of the proof of popEquiv to
       move the text insertion point there.

    5) Press the "TreeItem" button to select the corresponding item in the
       tree.

    6) Press "Selected" to move the Coq derivation to that point.

    7) Now press "Replay" twice to replay the next two steps.  Notice
       how the "H" in each tactic is updated to "H0"

Lemma extraction scenario:

    1) Start CoqPIE with:

       cd CoqPIE
       python project.py -p prover.pp
       (after doing ./buildSmall and closing the editor--there
        seems to be a bug when editing directly after the buildSmall)

    2) Select "../Small/Model.v" in the treeview window on the left.  Click the
       triangle to the left of the text to expand the entry.

    3) Edit the text to uncomment all commented constructs (in Exp, eval, pop,
       noFind, noRef and popEquiv)

    4) Go to the "mergePredicates" theorem and place the text cursor on top of
       "eapply validateTransitive"

    5) Click "TreeItem" to select the corresponding line in the tree at the
       left

    6) From the pull down menu select "Macros->Extract lemma"
