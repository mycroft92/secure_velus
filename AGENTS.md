This is my thesis work built on top of Velus compiler toolchain.
I am implementing the following paper (written by me):

1. Read the STC_translation_preservation-2.pdf 

General instructions:
- The readme.md is written by Velus team, not by me.
- Velus is a compiler for Lustre language, it is split into multiple phases (Lustre, NLustre, STC, Obc) lowering to CLight gradually (which is similar to C)
- The code relevant to my work is implemented in SIF folder. Understand this implementation
- Avoid reading from Compcert folder as much as possible.
- Avoid modifying Velus team's code as much possible (unless required by my paper)
- Avoid reading Obc, ObcToClight, StcToObc, Transcription folders. They are not relevant to the work we are doing for now.
- Each phase is usually self-contained in a similarly named folder, except when moving from phase to phase
- When you add a file/folder modify the vfiles to reflect the compilation, do a make clean and then configure with `./configure -clightgen x86_64-linux`. If existing files are modified, you don't need to do this step.
- Update TODO.md whenever you perform a task (create it if needed)
- Document every decision clearly before proceeding.
- Before starting make a new branch called AI_version from the current state and then make your changes only in that branch. Merge only on approval

Tasks to do:
We are to implement the  paper mentioned as close as possible but the important thing is to prove the correctness (so you can take alternate design decisions if it lets you make the proof.)

In order to implement the security typesystem for NLustre, I wrote the file `SecNLusTyping.v`. `SecSTCTyping.v` serves a similar purpose for STC phase. The main theorem I want to prove is that the types are preserved in translation from NLustre to STC. However expressing this has become a challenge because my name generation has to be exactly the same. I tried to remedy that situtation with `NameInterface.v` to a certain extent. 
Help me state and then prove the preservation theorem, rough ideas are present in `SecNLusStcTranslation.v` for both statement and proof. Use that as the starting point.