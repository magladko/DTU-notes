- Examine the program and find all object constructors and VMT assignments.
    - List the actual addresses of the VMTs and constructors.
    - Make sure that the functions you found are actually constructors!


|               | VMT addr | Constructor | VMs count |
| ------------- | -------- | ----------- | --------- |
| CZizala       | 414570   | 4010E0      | 14        |
| CUnknown      | 4147A4   | 40F030      | 4         |
| IUnknown      | -        |             |           |
| IZizala       | -        |             |           |
| CZizalaApp    | 4145F8   | 401A70      | 17        |
| IZizalaApp    | -        |             |           |
| CZizaliWindow | 414678   | 402220      | 6         |
| IZizaliWindow | -        |             |           |
| CObrazovka    | 4146A4   | 402900      | 10        |
| IObrazovka    | -        |             |           |

TODO: hierarchy

- From VMTs discover the numbers of virtual methods for each class.
- Find those class names and the class hierarchy from the RTTI information.
- Describe the class hierarchy.
    - In your description you should explain specifically which part of the data supports your hierarchy and prevents alternative hierarchies.
    - You will find that the hierarchy is a bit strange. List the strange parts and explain what is their meaning and what is the cause of them. Your explanation does not have to be completely accurate (from the binary, you can’t easily decide which of several causes was the real one), but it should be consistent with the observed facts.