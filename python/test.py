from collections import deque



max_number = 7



index_pool = deque(range(max_number))
print(index_pool)

index_pool.rotate(1)
print(index_pool)


