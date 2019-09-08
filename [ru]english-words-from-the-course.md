# Английские слова с курса Algorithms: part 1

## Глаголы (verbs)

- to state - утвердить, сформулировать (state them explicitly - сформулировать их явно)
- to maintain - поддерживать (... and make sure that our algorithms maintain those properties)
- to articulate - сформулировать (we can articulate an API for generic stacks)
- to encounter - сталкиваться (столкновение без to)
- to persuade - убедить (to persuade ourselves)
- to acquire - приобретать
- to tend - имеет тенденцию или “как правило”
- to assume - предполагать
- to lead to - приводить к
- to occur - происходить
- to speed up - ускорять
- to worth (ed) - стоить
- to strike (strike - struck [strʌk] - stricken [strɪkən]) - поражать
- to violate - нарушать
- to interleave - прослаивать / чередовать (interleaved - чередующийся)
- to point out - указывает, показывает
- to sweep sth - прочесать что-л., чистить что-л.

## Существительные (nouns)

- flaw - недостаток (так же и downside)
- boost - ускорение (форсировать)
- worth - ценность, цена
- inquiry - исследование (scientific inquiry)
- stride - шаг, большой шаг (может быть в смысле успеха)

## Предлоги (Prepositions)

- in a plane - на плоскости (стереометрия)
  не ~~on a plane~~
- on the Convex Hull - на выпуклой оболочке

## Прилагательные (adjectives)

- porous - пористый
- error-prone - склонный к ошибкам
- tedious - нудный, утомительный (tedious to count exactly)
- shallow - небольшой (shallow memory usage)
- negligible - незначительный (the object overhead is negligible as n gets large)
- comprised of - состоящая из
- embedded system - встроенная система
- ongoing - постоянный / непрерывный
- promising - перспективный
- sophisticated - сложный
- essential [или substantial] - существенный
- worthwhile - стоящий
- requisite (R`E) - необходимый
- a fudge factor - фиктивный коэффициент
- backward - обратный
- indicative - показательный, ориентировачный
- planar - плоский (треугольник)

## Наречие (adverbs)

- ahead of time - досрочно (we required clients to provide the maximum capacity of the stack ahead of time)
- mutually - обоюдно
- on the contrary - напротив
- backwards - назад, в обратном направлении

## Союзы (conjuctions)

- Because of - из-за

## Обычные и устойчивые фразы (phrases + idioms)

- all the way down to code - вплоть до кода

- you may end up working with - вы можете в конечном итоге работая с..

- to bear in mind - имейте в виду

- is going to have - будет иметь место

- rather than - скорее чем

- this is the idea, that - идея состоит в том, чтобы

- struck by lightning - поражен молнией

- Her delegation believed that, on the contrary, the Special Committee had an important contribution to make in that area. - Ее делегация считает, что наоборот Специальный комитет может внести важный вклад в это дело.

- ...that is more clear,... than would otherwise be possible - чем это было бы возможно в противном случае  

- every element goes all the way back - каждый элемент проходит весь путь обратно (в сортировке)

- so this is when the items come in in reverse order - это когда (на анимацию смотрит) элементы приходят в (два in) обратном порядке

- there's also a good case that actually we take advantage of in plenty of practical applications - есть также хор. пример того, что мы используем его во многих практических целях.

- Each item (except the first) is compared against the item to its left (and to no other items), for a total of n−1 compares.

- we go backwards through the array - мы идем назад через массив.

- gets us to the next increment - переводит нас к следующему инкременту.

- a uniformly random permutation of <== assuming real numbers uniformly at random - равномерно распределенный
  we can say "randomly and uniformly" without worrying about making a mistake.

- throw a point 3 out - выкидываем точку 3 отсюда

## Definitions

Deque - a linear data structure in which elements may be appended to or removed from either end.

Circumference (окружность) - the length of the closed curve of a circle(круг).
  - the boundary line encompassing an area or objectю

## Code descriptions, comments

- Given a reference `first` to the first node of a null-terminated linked list with at least two nodes, what does the code fragment below do?

    ```Java
    Node x = first;
    while (x.next.next != null) {
        x = x.next;
    }
    x.next = null;
    ```

    Upon termination of the loop, `x` is a reference to the second to last node. [ru: по завершению цикла, х - это ссылка на второй с конца узел] The final statement deletes the last node from the list.
