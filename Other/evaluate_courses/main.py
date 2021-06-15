def read_from_file(filename):
    with open(filename) as f:
        text = f.read()
    lines = [i.split('\t') for i in text.split('\n')]
    for l in lines:
        l[1] = int(l[1])
        l[2] = float(l[2])
        l[3] = float(l[3])
        l[4] = float(l[4])
        l[5] = int(l[5])
        l[6] = l[6] == '1'

    return lines


courses = read_from_file('courses.txt')


# 0: 名称
# 1: 开设学期
# 2: 学分
# 3: 总学时
# 4: 实验或上机学时
# 5: 类别(0或1)
# 6: 是否为双语课程

def evaluate(courses):
    def balance(sem):
        return 4 * sem[0] + sem[1]

    sem = [0, 0, 0]
    scr_0, scr_1 = 0, 0
    ti, ti_exp = 0, 0
    bi = 0
    for c in courses:
        sem[c[1] - 5] += 1
        ti += c[3]
        if c[5] == 0:
            ti_exp += c[4]
            scr_0 += c[2]
            if c[6]:
                bi += 1
        else:
            scr_1 += c[2]
    if not (scr_0 >= 9 - 4 and ti_exp >= 32 - 12 and bi >= 1 and scr_1 >= 7):
        return float('-inf')
    return (-1) * ti + \
           (-10) * (scr_0 + scr_1) + \
           (+8) * balance(sem)


def select(seq, num):
    result = []
    temp, index = num, 0
    while temp:
        if temp & 1:
            result.append(seq[index])
        temp, index = temp >> 1, index + 1
    return result


def try_all():
    result = []
    selection = (1 << len(courses)) - 1
    while selection:
        combination = select(courses, selection)
        score = evaluate(combination)
        if score != float('-inf'):
            result.append((selection, score))
        selection -= 1
    result.sort(key=lambda ele: ele[1], reverse=True)
    return result


selections = try_all()
print(len(selections), 'eligible combinations are found.')
for s in selections[:20]:
    print(''.join(reversed(bin(s[0])[2:].zfill(len(courses)))), ': score =', s[1])
    print([c[0] for c in select(courses, s[0])])

# print(evaluate(select(courses, 0b11100100000111)))
