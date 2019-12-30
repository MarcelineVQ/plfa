things I have learned so far reading other people's agda code

If you can avoid using _ then do so.
It's cute, awesome, and sometimes unavoidable, to let the compiler insert a value for you. But annotate it in a comment! Because now your reader has to also compute what goes in that spot!

Prefer mutual over forward declarations. People reading your defintions should be able to refer to the type at-will, not have to search for it.

import explicitly, you might use many things from Module.Foo.Baz but it's going to help me to know what those things are upfront

