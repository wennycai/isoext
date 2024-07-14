from src.broker import starting_curve
from src.randomideal import random_ideal
from src.correspondence import constructive_deuring, constructive_deuring_new, constructive_deuring_2, constructive_deuring_new_2
from sage.all import *

x = var("x")
#p3923
# p = 23759399264157352358673788613307970528646815114090876784643387662192449945599
# new p
p = 88881583528687251695085351202716893361162950661419911309645115899579883741851
# p = 82460884298062985073154572827668830392815810118105762484859341606469999173287
p = 95008112981120315885997172640930988762706307039235815007466698894954688225259
F2 = GF(p**2, name = "i", modulus = x**2+1)
#p2
#p = 37670568336551536389503919665937491111216122470333837677213877442445311999999
#F2 = GF(p**2, name = "i", modulus = x**2+1)
#p1
# p = 11956566944641502957704189594909498993478297403838643406058180334130656750161
# F2 = GF(p**2, name = "i", modulus = x**2+17)

t = cputime()
E0, iota, O0 = starting_curve(F2)
print("The runtime of constructing E0:",cputime(t),"s")
# print(E0)
# print(O0)
t1 = 0
t2 = 0
t3 = 0
t4 = 0
num = 1
for ii in range(num):
    I = random_ideal(O0)
    t = cputime()
    E2, phi2, _ = constructive_deuring_new(I, E0, iota)
    t1+=cputime(t)
    t = cputime()
    E1, phi, _ = constructive_deuring(I, E0, iota)
    t2+=cputime(t)
    t = cputime()
    E2, phi2, _ = constructive_deuring_new_2(I, E0, iota)
    t3+=cputime(t)
    # t = cputime()
    # E1, phi, _ = constructive_deuring_2(I, E0, iota)
    # t4+=cputime(t)
print("==================================================")
print("The original algorithm for computing constructive deuring correspondence takes",t2/num,"s")
print("The new algorithm for computing constructive deuring correspondence takes",t1/num,"s")
print("The new algorithm for computing constructive deuring correspondence (adjust cost model) takes",t3/num,"s")
# print("The original algorithm for computing constructive deuring correspondence (adjust cost model) takes",t4/num,"s")