add_library(PassedWaitingList
	PWList.cpp
	WaitingList.cpp
)


add_dependencies(PassedWaitingList pardibaal-ext sparsehash-ext)