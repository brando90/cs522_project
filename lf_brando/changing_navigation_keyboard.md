
On Mac OS X, in `~/Library/Application\ Support/coq/` is where the file is, but do command:

> vim ~/Library/Application\ Support/coq/coqiderc

(3) Edit the file `coqiderc` and make the following change:

|before | modifier_for_navigation = `"<Control>"` | 
|after | modifier_for_navigation = `"<Shift><Primary>"` |

----
Note:

`<Primary>` is the funny apple key button.

----

https://github.com/coq/coq/wiki/Configuration-of-CoqIDE
https://stackoverflow.com/questions/53464325/how-do-you-tell-the-coqide-i-want-to-use-the-apple-keyboard-command-for-naviga
